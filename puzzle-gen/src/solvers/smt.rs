//! SMT-LIB compatible solver backend.

use std::collections::HashMap;

use log::{error, trace};
use smtlib::lowlevel::{
    ast::{self},
    lexicon::{self},
};
use smtlib::terms::{Dynamic, STerm, Sorted, StaticSorted};

use crate::solvers::{Backend, QueryResult};
use crate::theories::{
    Atom, Axiom, AxiomBody, ConstId, Formula, Instance, SortId, SymbolId, Term, VarId,
};

/// Create a non-standard option with an optional argument.
fn make_option<'st>(name: &'st str, arg: Option<&'st str>) -> smtlib::lowlevel::ast::Option<'st> {
    let kw = lexicon::Keyword(name);
    match arg {
        Some(sym) => ast::Option::Attribute(ast::Attribute::WithValue(
            kw,
            ast::AttributeValue::Symbol(lexicon::Symbol(sym)),
        )),
        None => ast::Option::Attribute(ast::Attribute::Keyword(kw)),
    }
}

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
/// TODO: This is tested against CVC5, it shouldn't be expected to work with Z3
/// out-of-the-box. In particular, we rely on CVC5's finite model finding
/// capabilities.
fn configure_solver<'st, B: smtlib::Backend>(
    solver: &mut smtlib::Solver<'st, B>,
) -> Result<(), smtlib::Error> {
    use smtlib::lowlevel::ast::Option;
    // enable model production and unsat core
    set_option(solver, Option::ProduceModels(true))?;
    trace!("set produce-models true");
    set_option(solver, Option::ProduceUnsatCores(true))?;
    trace!("set produce-unsat-cores true");

    // enable finite model finder (probably CVC5-specific, so swallow errors if
    // unsupported.)
    let finite_model_find = make_option("finite-model-find", Some("true"));
    if let Err(err) = set_option(solver, finite_model_find) {
        error!("error: {err:?}");
        return Err(err);
    }
    trace!("set finite-model-find true");

    // set the logic to UFDT (uninterpreted functions with algebraic data types)
    // let logic_ufdt = smtlib::Logic::Custom("UFDT".to_string());
    // solver.set_logic(logic_ufdt)?;
    // trace!("set logic to UFDT");
    Ok(())
}

/// Backend over SMT-LIB compatible solvers.
///
/// The `Storage` must outlive the backend; the caller owns it and passes a
/// reference in at construction time, which avoids the self-referential
/// lifetime problem (Solver borrows Storage).
pub struct SmtBackend<'st, B: smtlib::Backend> {
    st: &'st smtlib::Storage,
    solver: smtlib::Solver<'st, B>,
    // Translation state, populated during load_instance.
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

        // NOTE: This currently performs a full clear-and-reload of the solver
        // state on every call, which is non-optimal: the puzzle-generation loop
        // calls this once per ablation step, re-translating every fact and
        // axiom each time. A future revision should keep a long-lived solver
        // session and use push/pop scopes (or incremental assert/retract of
        // axioms) so that only the changed pieces are sent to the solver.
        let theory = instance.theory();

        self.smt_sorts.clear();
        self.smt_consts.clear();
        self.smt_domain_consts.clear();
        self.smt_fun_names.clear();
        self.smt_fun_ret_sorts.clear();

        trace!("loading sorts");
        // 1. Register sorts (actual declaration happens when first used by
        //    declare_fun / declare_const inside the solver).
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

        trace!("loading consts");
        // 2. Declare domain constants and assert distinctness per sort.
        for (sort_id, constants) in instance.domain() {
            let sort = self.smt_sorts[sort_id];
            let mut const_dynamics: Vec<Dynamic<'st>> = Vec::new();

            for &const_id in constants {
                let name = self.st.alloc_str(instance.constant(const_id).name());
                let c = sort.new_const(self.st, name);
                let dynamic: Dynamic<'st> = c.into();
                self.smt_domain_consts.insert(const_id, dynamic);
                const_dynamics.push(dynamic);
            }

            if const_dynamics.len() > 1 {
                let terms: Vec<&'st ast::Term<'st>> =
                    const_dynamics.iter().map(|d| d.term()).collect();
                let distinct = self.smt_app("distinct", &terms);
                self.solver.assert(self.to_bool(distinct))?;
            }
        }

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

        // 4. Assert ground facts.
        trace!("asserting ground facts");
        let empty_var_map = HashMap::new();
        for fact in instance.facts() {
            let b = self.translate_atom(fact, &empty_var_map);
            self.solver.assert(b)?;
        }

        // 5. Assert active axioms.
        trace!("asserting active axioms");
        for &axiom_id in instance.active_axioms() {
            let axiom = theory.axiom(axiom_id);
            let b = self.translate_axiom(axiom);
            self.solver.assert(b)?;
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
