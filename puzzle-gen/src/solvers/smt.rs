//! SMT-LIB compatible solver backend.

use std::collections::{HashMap, HashSet};

use log::trace;
use smtlib::lowlevel::{
    ast::{self},
    lexicon::{self},
};
use smtlib::terms::{Dynamic, STerm, Sorted, StaticSorted};

use crate::solvers::{Backend, QueryResult};
use crate::theories::{
    Atom, Axiom, AxiomBody, ConstId, Formula, Instance, SortId, SymbolId, Term, VarId, body_holds,
    enumerate_bindings, eval_term,
};

/// Set an option for the solver.
fn set_option<'st, B: smtlib::Backend>(
    solver: &mut smtlib::Solver<'st, B>,
    option: smtlib::lowlevel::ast::Option<'st>,
) -> Result<smtlib::lowlevel::ast::GeneralResponse<'st>, smtlib::Error> {
    let cmd = ast::Command::SetOption(option);
    solver.run_command(cmd)
}

/// Configure the SMT solver backend for use with model finding. Specifically,
/// it sets the correct logic and solver options.
///
/// Note: tested against CVC5. Z3 support is not guaranteed.
fn configure_solver<'st, B: smtlib::Backend>(
    solver: &mut smtlib::Solver<'st, B>,
) -> Result<(), smtlib::Error> {
    use smtlib::lowlevel::ast::Option;
    set_option(solver, Option::ProduceModels(true))?;
    trace!("set produce-models true");
    set_option(solver, Option::ProduceUnsatCores(true))?;
    trace!("set produce-unsat-cores true");
    solver.set_logic(smtlib::Logic::Custom("ALL".to_string()))?;
    Ok(())
}

// -- Closed-world helpers --------------------------------------------------

/// Enumerate all ground tuples for a sequence of sort IDs.
fn enumerate_ground_tuples(
    sorts: &[SortId],
    domain: &HashMap<SortId, Vec<ConstId>>,
) -> Vec<Vec<ConstId>> {
    sorts.iter().fold(vec![vec![]], |acc, &sort| {
        let consts = domain.get(&sort).map_or(&[] as &[ConstId], Vec::as_slice);
        acc.into_iter()
            .flat_map(|t| {
                consts.iter().map(move |&c| {
                    let mut t = t.clone();
                    t.push(c);
                    t
                })
            })
            .collect()
    })
}

/// Compute the least fixed point (LFP) of the active Horn axioms over the
/// finite domain. Naïve forward-chaining: iterate until no new atoms are
/// derived. Returns the set of all ground predicate atoms that hold.
fn compute_lfp(instance: &Instance<'_>) -> HashSet<(SymbolId, Vec<ConstId>)> {
    let theory = instance.theory();
    let domain = instance.domain();

    // Seed with explicit positive ground predicate facts.
    let mut lfp: HashSet<(SymbolId, Vec<ConstId>)> = instance
        .facts()
        .iter()
        .filter_map(|atom| match atom {
            Atom::Predicate { symbol, args } => args
                .iter()
                .map(|t| match t {
                    Term::DomainConst(c) => Some(*c),
                    _ => None,
                })
                .collect::<Option<Vec<_>>>()
                .map(|cs| (*symbol, cs)),
            _ => None,
        })
        .collect();

    loop {
        let mut added = false;
        for &axiom_id in instance.active_axioms() {
            let axiom = theory.axiom(axiom_id);
            if let AxiomBody::Horn { body, head } = axiom.body()
                && let Atom::Predicate {
                    symbol: head_sym,
                    args: head_args,
                } = head
            {
                for binding in enumerate_bindings(axiom.vars(), domain) {
                    if body_holds(body, &binding, &lfp) {
                        let ground: Option<Vec<ConstId>> =
                            head_args.iter().map(|t| eval_term(t, &binding)).collect();
                        if let Some(args) = ground
                            && lfp.insert((*head_sym, args))
                        {
                            added = true;
                        }
                    }
                }
            }
        }
        if !added {
            break;
        }
    }

    lfp
}

/// Backend over SMT-LIB compatible solvers.
///
/// The `Storage` must outlive the backend; the caller owns it and passes a
/// reference in at construction time, which avoids the self-referential
/// lifetime problem (Solver borrows Storage).
pub struct SmtBackend<'st, B: smtlib::Backend> {
    st: &'st smtlib::Storage,
    solver: smtlib::Solver<'st, B>,
    // True after the first load_instance call; sorts/symbols/consts are permanent.
    declarations_done: bool,
    // True when a per-instance assertion scope is currently pushed.
    instance_scope_active: bool,
    // Translation state, populated on first load_instance and reused thereafter.
    smt_sorts: HashMap<SortId, smtlib::sorts::Sort<'st>>,
    smt_consts: HashMap<SymbolId, Dynamic<'st>>,
    smt_domain_consts: HashMap<ConstId, Dynamic<'st>>,
    smt_fun_names: HashMap<SymbolId, &'st str>,
    smt_fun_ret_sorts: HashMap<SymbolId, smtlib::sorts::Sort<'st>>,
}

impl<'st, B: smtlib::Backend> SmtBackend<'st, B> {
    pub fn new(st: &'st smtlib::Storage, backend: B) -> Result<Self, smtlib::Error> {
        let mut solver = smtlib::Solver::new(st, backend)?;
        trace!("constructed solver");
        configure_solver(&mut solver)?;
        trace!("configured solver");
        Ok(Self {
            st,
            solver,
            declarations_done: false,
            instance_scope_active: false,
            smt_sorts: HashMap::new(),
            smt_consts: HashMap::new(),
            smt_domain_consts: HashMap::new(),
            smt_fun_names: HashMap::new(),
            smt_fun_ret_sorts: HashMap::new(),
        })
    }

    /// Build an SMT-LIB function/predicate application term.
    fn smt_app(&self, name: &'st str, args: &[&'st ast::Term<'st>]) -> ast::Term<'st> {
        let qi = ast::QualIdentifier::Identifier(ast::Identifier::Simple(lexicon::Symbol(name)));
        if args.is_empty() {
            ast::Term::Identifier(qi)
        } else {
            ast::Term::Application(qi, self.st.alloc_slice(args))
        }
    }

    /// Wrap a lowlevel term as a `Bool`.
    fn to_bool(&self, term: ast::Term<'st>) -> smtlib::Bool<'st> {
        STerm::new(self.st, term).into()
    }

    /// Translate our IR `Term` into an smtlib `Dynamic`.
    fn translate_term(&self, term: &Term, var_map: &HashMap<VarId, Dynamic<'st>>) -> Dynamic<'st> {
        match term {
            Term::Var(v) => var_map[v],
            Term::Const(sym) => self.smt_consts[sym],
            Term::DomainConst(c) => self.smt_domain_consts[c],
            Term::App { symbol, args } => {
                let name = self.smt_fun_names[symbol];
                let arg_terms: Vec<&'st ast::Term<'st>> = args
                    .iter()
                    .map(|a| self.translate_term(a, var_map).term())
                    .collect();
                let smt_term = self.smt_app(name, &arg_terms);
                Dynamic::from_term_sort(
                    STerm::new(self.st, smt_term),
                    self.smt_fun_ret_sorts[symbol],
                )
            }
        }
    }

    /// Translate our IR `Atom` into an smtlib `Bool`.
    fn translate_atom(
        &self,
        atom: &Atom,
        var_map: &HashMap<VarId, Dynamic<'st>>,
    ) -> smtlib::Bool<'st> {
        match atom {
            Atom::Predicate { symbol, args } => {
                let name = self.smt_fun_names[symbol];
                let arg_terms: Vec<&'st ast::Term<'st>> = args
                    .iter()
                    .map(|a| self.translate_term(a, var_map).term())
                    .collect();
                self.to_bool(self.smt_app(name, &arg_terms))
            }
            Atom::Eq(t1, t2) => {
                let a = self.translate_term(t1, var_map);
                let b = self.translate_term(t2, var_map);
                a._eq(b)
            }
            Atom::Neq(t1, t2) => {
                let a = self.translate_term(t1, var_map);
                let b = self.translate_term(t2, var_map);
                a._neq(b)
            }
        }
    }

    /// Translate our IR `Formula` into an smtlib `Bool`.
    fn translate_formula(
        &self,
        formula: &Formula,
        var_map: &HashMap<VarId, Dynamic<'st>>,
    ) -> smtlib::Bool<'st> {
        match formula {
            Formula::Atom(atom) => self.translate_atom(atom, var_map),
            Formula::And(fs) => {
                let bools: Vec<_> = fs
                    .iter()
                    .map(|f| self.translate_formula(f, var_map))
                    .collect();
                self.make_and(&bools)
            }
            Formula::Or(fs) => {
                let bools: Vec<_> = fs
                    .iter()
                    .map(|f| self.translate_formula(f, var_map))
                    .collect();
                self.make_or(&bools)
            }
            Formula::Not(f) => !self.translate_formula(f, var_map),
            Formula::Implies(lhs, rhs) => {
                let l = self.translate_formula(lhs, var_map);
                let r = self.translate_formula(rhs, var_map);
                l.implies(r)
            }
            Formula::Forall(vars, body) => {
                let (sorted_vars, inner_map) = self.bind_vars(vars, var_map);
                let body_bool = self.translate_formula(body, &inner_map);
                self.wrap_forall(&sorted_vars, body_bool)
            }
            Formula::Exists(vars, body) => {
                let (sorted_vars, inner_map) = self.bind_vars(vars, var_map);
                let body_bool = self.translate_formula(body, &inner_map);
                self.wrap_exists(&sorted_vars, body_bool)
            }
        }
    }

    /// Translate a full `Axiom` (including its implicit universal quantifier)
    /// into an smtlib `Bool`.
    fn translate_axiom(&self, axiom: &Axiom) -> smtlib::Bool<'st> {
        let (sorted_vars, var_map) = self.bind_vars(axiom.vars(), &HashMap::new());

        let body_bool = match axiom.body() {
            AxiomBody::Horn { body, head } => {
                let head_bool = self.translate_atom(head, &var_map);
                if body.is_empty() {
                    head_bool
                } else {
                    let body_bools: Vec<_> = body
                        .iter()
                        .map(|a| self.translate_atom(a, &var_map))
                        .collect();
                    self.make_and(&body_bools).implies(head_bool)
                }
            }
            AxiomBody::Integrity { body } => {
                let body_bools: Vec<_> = body
                    .iter()
                    .map(|a| self.translate_atom(a, &var_map))
                    .collect();
                !self.make_and(&body_bools)
            }
            AxiomBody::FunctionalFact {
                symbol,
                args,
                value,
            } => {
                let name = self.smt_fun_names[symbol];
                let arg_terms: Vec<&'st ast::Term<'st>> = args
                    .iter()
                    .map(|a| self.translate_term(a, &var_map).term())
                    .collect();
                let app = Dynamic::from_term_sort(
                    STerm::new(self.st, self.smt_app(name, &arg_terms)),
                    self.smt_fun_ret_sorts[symbol],
                );
                let val = self.translate_term(value, &var_map);
                app._eq(val)
            }
            AxiomBody::General(formula) => self.translate_formula(formula, &var_map),
        };

        if sorted_vars.is_empty() {
            body_bool
        } else {
            self.wrap_forall(&sorted_vars, body_bool)
        }
    }

    // -- Quantifier / connective helpers ------------------------------------

    /// Create smtlib sorted-variable bindings and extend the var_map.
    fn bind_vars(
        &self,
        vars: &[(VarId, SortId)],
        parent_map: &HashMap<VarId, Dynamic<'st>>,
    ) -> (Vec<ast::SortedVar<'st>>, HashMap<VarId, Dynamic<'st>>) {
        let mut map = parent_map.clone();
        let mut sorted = Vec::with_capacity(vars.len());

        for &(var_id, sort_id) in vars {
            let var_name = self.st.alloc_str(&format!("_v{}", var_id.0));
            let sort = self.smt_sorts[&sort_id];

            sorted.push(ast::SortedVar(lexicon::Symbol(var_name), sort.ast()));

            // Build a term that references this quantified variable.
            let qi = ast::QualIdentifier::Sorted(
                ast::Identifier::Simple(lexicon::Symbol(var_name)),
                sort.ast(),
            );
            let dynamic =
                Dynamic::from_term_sort(STerm::new(self.st, ast::Term::Identifier(qi)), sort);
            map.insert(var_id, dynamic);
        }

        (sorted, map)
    }

    fn wrap_forall(
        &self,
        vars: &[ast::SortedVar<'st>],
        body: smtlib::Bool<'st>,
    ) -> smtlib::Bool<'st> {
        let vars_slice = self.st.alloc_slice(vars);
        self.to_bool(ast::Term::Forall(vars_slice, body.term()))
    }

    fn wrap_exists(
        &self,
        vars: &[ast::SortedVar<'st>],
        body: smtlib::Bool<'st>,
    ) -> smtlib::Bool<'st> {
        let vars_slice = self.st.alloc_slice(vars);
        self.to_bool(ast::Term::Exists(vars_slice, body.term()))
    }

    fn make_and(&self, bools: &[smtlib::Bool<'st>]) -> smtlib::Bool<'st> {
        match bools.len() {
            0 => smtlib::Bool::new(self.st, true),
            1 => bools[0],
            _ => {
                let terms: Vec<_> = bools.iter().map(|b| b.term()).collect();
                self.to_bool(self.smt_app("and", &terms))
            }
        }
    }

    fn make_or(&self, bools: &[smtlib::Bool<'st>]) -> smtlib::Bool<'st> {
        match bools.len() {
            0 => smtlib::Bool::new(self.st, false),
            1 => bools[0],
            _ => {
                let terms: Vec<_> = bools.iter().map(|b| b.term()).collect();
                self.to_bool(self.smt_app("or", &terms))
            }
        }
    }
}

impl<'st, B: smtlib::Backend> Backend for SmtBackend<'st, B> {
    type Error = smtlib::Error;

    fn load_instance(&mut self, instance: &Instance<'_>) -> Result<(), Self::Error> {
        trace!("loading instance");
        let theory = instance.theory();

        // Pop the previous instance's assertion scope (if any) to clear all
        // per-instance assertions. Declarations are permanent and survive this.
        if self.instance_scope_active {
            self.solver.run_command(ast::Command::Pop(lexicon::Numeral::from_usize(1)))?;
            self.instance_scope_active = false;
        }

        if !self.declarations_done {
            // First call only: declare sorts, domain constants, and symbols.
            // These are permanent — they survive pop and must not be re-sent.

            trace!("declaring sorts");
            // 1. Register sort descriptors (no solver command; sorts are
            //    declared implicitly when first used in declare_fun).
            for (id, decl) in theory.sorts() {
                let name = self.st.alloc_str(decl.name());
                let sort = smtlib::sorts::Sort::Dynamic {
                    st: self.st,
                    name,
                    index: &[],
                    parameters: &[],
                };
                self.smt_sorts.insert(id, sort);
            }

            trace!("declaring domain constants");
            // 2. Declare domain constants explicitly via declare_fun (0-arity)
            //    so the declarations reach the solver before any push scope.
            //    Using sort.new_const would lazily emit declare-const on first
            //    assert use, which would land inside the scope and get popped.
            for (sort_id, constants) in instance.domain() {
                let sort = self.smt_sorts[sort_id];
                for &const_id in constants {
                    let const_name = instance.constant(const_id).name();
                    let fun = smtlib::funs::Fun::new(self.st, const_name, vec![], sort);
                    self.solver.declare_fun(&fun)?;
                    let name = self.st.alloc_str(const_name);
                    let qi = ast::QualIdentifier::Identifier(
                        ast::Identifier::Simple(lexicon::Symbol(name)),
                    );
                    let dynamic =
                        Dynamic::from_term_sort(STerm::new(self.st, ast::Term::Identifier(qi)), sort);
                    self.smt_domain_consts.insert(const_id, dynamic);
                }
            }

            trace!("declaring predicate/function symbols");
            // 3. Declare predicate / function symbols.
            for (id, decl) in theory.symbols() {
                if let Some(sig) = decl.signature() {
                    let name = self.st.alloc_str(decl.name());
                    self.smt_fun_names.insert(id, name);

                    let param_sorts: Vec<smtlib::sorts::Sort<'st>> =
                        sig.params().iter().map(|s| self.smt_sorts[s]).collect();
                    let ret_sort = match sig.ret() {
                        None => smtlib::sorts::Sort::Static(smtlib::Bool::AST_SORT),
                        Some(s) => self.smt_sorts[&s],
                    };
                    self.smt_fun_ret_sorts.insert(id, ret_sort);

                    let fun = smtlib::funs::Fun::new(self.st, decl.name(), param_sorts, ret_sort);
                    self.solver.declare_fun(&fun)?;
                }
            }

            self.declarations_done = true;
        }

        // Push a fresh scope for this instance's assertions. Everything
        // asserted below will be cleared when this scope is popped.
        self.solver.run_command(ast::Command::Push(lexicon::Numeral::from_usize(1)))?;
        self.instance_scope_active = true;

        let empty_var_map = HashMap::new();

        // 4. Assert per-sort distinctness and coverage constraints.
        trace!("asserting domain constraints");
        for (sort_id, constants) in instance.domain() {
            let sort = self.smt_sorts[sort_id];
            let const_dynamics: Vec<Dynamic<'st>> = constants
                .iter()
                .map(|&c| self.smt_domain_consts[&c])
                .collect();

            if const_dynamics.len() > 1 {
                let terms: Vec<&'st ast::Term<'st>> =
                    const_dynamics.iter().map(|d| d.term()).collect();
                let distinct = self.smt_app("distinct", &terms);
                self.solver.assert(self.to_bool(distinct))?;
            }

            // Coverage axiom: tells the solver the sort has *exactly* these
            // constants, making quantifier instantiation finite.
            if !const_dynamics.is_empty() {
                let var_name = self.st.alloc_str("_cov");
                let var_binder = ast::SortedVar(lexicon::Symbol(var_name), sort.ast());
                let var_qi = ast::QualIdentifier::Sorted(
                    ast::Identifier::Simple(lexicon::Symbol(var_name)),
                    sort.ast(),
                );
                let var_dyn = Dynamic::from_term_sort(
                    STerm::new(self.st, ast::Term::Identifier(var_qi)),
                    sort,
                );
                let disjuncts: Vec<smtlib::Bool<'st>> =
                    const_dynamics.iter().map(|c| var_dyn._eq(*c)).collect();
                let body = self.make_or(&disjuncts);
                let coverage = self.wrap_forall(&[var_binder], body);
                self.solver.assert(coverage)?;
            }
        }

        // 5. Assert ground facts.
        trace!("asserting ground facts");
        for fact in instance.facts() {
            let b = self.translate_atom(fact, &empty_var_map);
            self.solver.assert(b)?;
        }

        // 6. Assert active axioms.
        trace!("asserting active axioms");
        for &axiom_id in instance.active_axioms() {
            let axiom = theory.axiom(axiom_id);
            let b = self.translate_axiom(axiom);
            self.solver.assert(b)?;
        }

        // 7. Assert CWA negations: for every ground predicate atom not in the
        //    LFP of the active Horn axioms, assert its negation.
        trace!("computing LFP for CWA");
        let lfp = compute_lfp(instance);
        trace!("asserting CWA negations ({} atoms in LFP)", lfp.len());
        for (id, decl) in theory.symbols() {
            if let Some(sig) = decl.signature() {
                if sig.ret().is_some() {
                    continue; // skip functions; CWA applies only to predicates
                }
                for args in enumerate_ground_tuples(sig.params(), instance.domain()) {
                    if !lfp.contains(&(id, args.clone())) {
                        let atom = Atom::Predicate {
                            symbol: id,
                            args: args.into_iter().map(Term::DomainConst).collect(),
                        };
                        let b = self.translate_atom(&atom, &empty_var_map);
                        self.solver.assert(!b)?;
                    }
                }
            }
        }

        Ok(())
    }

    fn assert_axiom(&mut self, axiom: &Axiom) -> Result<(), Self::Error> {
        let b = self.translate_axiom(axiom);
        self.solver.assert(b)
    }

    fn check_entailment(&mut self, query: &Formula) -> Result<QueryResult, Self::Error> {
        trace!("starting entailment check");
        let q = self.translate_formula(query, &HashMap::new());

        // T union F union {not q} unsat  =>  q is entailed.
        let entailed = self.solver.scope(|solver| {
            solver.assert(!q)?;
            solver.check_sat()
        })?;
        if entailed == smtlib::SatResult::Unsat {
            return Ok(QueryResult::Entailed);
        }

        // T union F union {q} unsat  =>  not-q is entailed (q is refuted).
        let refuted = self.solver.scope(|solver| {
            solver.assert(q)?;
            solver.check_sat()
        })?;
        if refuted == smtlib::SatResult::Unsat {
            return Ok(QueryResult::Refuted);
        }

        Ok(QueryResult::Undetermined)
    }
}
