//! SMT-LIB compatible solver backend.

use std::collections::{HashMap, HashSet};

use log::trace;
use smtlib::lowlevel::{
    ast::{self, AttributeValue, GeneralResponse, GetUnsatCoreResponse, SpecificSuccessResponse},
    lexicon::{self, Keyword},
};
use smtlib::terms::{Dynamic, STerm, Sorted, StaticSorted};
use thiserror::Error;

use crate::bimulmap::BiMulMap;
use crate::solvers::{Backend, QueryResult};
use crate::theories::{
    Atom, Axiom, AxiomBody, AxiomId, ConstId, Formula, Instance, SortId, SymbolId, Term, VarId,
    enumerate_bindings,
};

#[derive(Debug, Error)]
pub enum SmtBackendError {
    #[error("unsupported feature: {0}")]
    Unsupported(String),
    #[error("general solver error: {0}")]
    General(String),
    #[error("solver error: {0}")]
    Solver(#[from] smtlib::Error),
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

/// Try to unify an atom's argument list with a ground fact tuple under the
/// current partial binding. Returns the extended binding on success, `None`
/// if any position conflicts.
fn unify_atom(
    args: &[Term],
    fact: &[ConstId],
    base: &HashMap<VarId, ConstId>,
) -> Option<HashMap<VarId, ConstId>> {
    if args.len() != fact.len() {
        return None;
    }
    let mut out = base.clone();
    for (arg, &c) in args.iter().zip(fact.iter()) {
        match arg {
            Term::Var(v) => match out.get(v).copied() {
                Some(existing) if existing != c => return None,
                None => {
                    out.insert(*v, c);
                }
                _ => {}
            },
            Term::DomainConst(d) => {
                if *d != c {
                    return None;
                }
            }
            // Function applications and theory-level constants can't be
            // unified against a ground fact tuple here. Fall back to leaving
            // the binding unconstrained on this atom (treat it as a non-join
            // constraint and let the SMT body handle it).
            Term::Const(_) | Term::App { .. } => return None,
        }
    }
    Some(out)
}

/// Extract the conjuncts of a formula body, treating a single `Atom` or an
/// `And` of formulas as a list. Used by existential specialization to find
/// atomic constraints to join against.
fn body_conjuncts(f: &Formula) -> Vec<&Atom> {
    match f {
        Formula::Atom(a) => vec![a],
        Formula::And(fs) => fs
            .iter()
            .filter_map(|g| match g {
                Formula::Atom(a) => Some(a),
                _ => None,
            })
            .collect(),
        _ => Vec::new(),
    }
}

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

/// Backend over SMT-LIB compatible solvers.
///
/// The `Storage` must outlive the backend; the caller owns it and passes a
/// reference in at construction time, which avoids the self-referential
/// lifetime problem (Solver borrows Storage).
pub struct SmtBackend<'st, B: smtlib::Backend> {
    st: &'st smtlib::Storage,
    solver: smtlib::Solver<'st, B>,
    // True after load_instance has run; calling it again is an error.
    loaded: bool,
    // Translation state, populated by load_instance.
    smt_sorts: HashMap<SortId, smtlib::sorts::Sort<'st>>,
    smt_consts: HashMap<SymbolId, Dynamic<'st>>,
    smt_domain_consts: HashMap<ConstId, Dynamic<'st>>,
    smt_fun_names: HashMap<SymbolId, &'st str>,
    smt_fun_ret_sorts: HashMap<SymbolId, smtlib::sorts::Sort<'st>>,
    // Snapshot of the loaded instance's domain, used for grounding quantifiers
    // in axioms and queries.
    smt_domain: HashMap<SortId, Vec<ConstId>>,
    // Predicates that are closed-world AND have no Horn-rule heads. Their
    // truth set is exactly the set of ground facts, which lets us specialize
    // bindings against them: when grounding a Horn body that references
    // `manages(z,y)`, only enumerate (z,y) values that actually appear as
    // ground facts — the rest are vacuous.
    ground_only_preds: HashSet<SymbolId>,
    // Per-predicate fact tuples, used by `specialize_bindings` to restrict
    // enumerations against ground-only predicates.
    ground_fact_index: HashMap<SymbolId, Vec<Vec<ConstId>>>,
    // Per-axiom activator literal name (`_act_aN`), in declaration order.
    // Each axiom is asserted as `(=> activator axiom)`; pinning the activator
    // turns the axiom on/off without re-asserting. A Vec preserves order
    // because cvc5 is sensitive to assertion order.
    activator_names: Vec<(AxiomId, &'st str)>,
    // AxiomId ↔ ground-clause names. Each axiom grounds to many `:named`
    // clauses (`_act_aN_i`); the reverse map lets `process_unsat_core` resolve
    // each clause in the unsat core back to its owning axiom.
    axiom_activators: BiMulMap<AxiomId, &'st str>,
    // Currently-active axioms (mirrors the latest Instance's set).
    active_axioms: HashSet<AxiomId>,
}

impl<'st, B: smtlib::Backend> SmtBackend<'st, B> {
    pub fn new(st: &'st smtlib::Storage, backend: B) -> Result<Self, smtlib::Error> {
        let mut solver = smtlib::Solver::new(st, backend)?;
        trace!("constructed solver");
        if std::env::var("PUZZLE_GEN_SMT_TRACE").is_ok() {
            solver.set_logger((
                |cmd: smtlib::lowlevel::ast::Command| eprintln!(">> {cmd}"),
                |_cmd: smtlib::lowlevel::ast::Command, res: &str| eprintln!("<< {res}"),
            ));
        }
        configure_solver(&mut solver)?;
        trace!("configured solver");
        Ok(Self {
            st,
            solver,
            loaded: false,
            smt_sorts: HashMap::new(),
            smt_consts: HashMap::new(),
            smt_domain_consts: HashMap::new(),
            smt_fun_names: HashMap::new(),
            smt_fun_ret_sorts: HashMap::new(),
            smt_domain: HashMap::new(),
            ground_only_preds: HashSet::new(),
            ground_fact_index: HashMap::new(),
            activator_names: Vec::new(),
            axiom_activators: BiMulMap::new(),
            active_axioms: HashSet::new(),
        })
    }

    /// Run a command and translate any errors.
    fn run_command(
        &mut self,
        cmd: ast::Command<'st>,
    ) -> Result<Option<SpecificSuccessResponse<'st>>, SmtBackendError> {
        let resp = self.solver.run_command(cmd)?;
        match resp {
            GeneralResponse::Success => Ok(None),
            GeneralResponse::SpecificSuccessResponse(resp) => Ok(Some(resp)),
            GeneralResponse::Unsupported => Err(SmtBackendError::Unsupported(cmd.to_string())),
            GeneralResponse::Error(e) => Err(SmtBackendError::General(e.to_string())),
        }
    }

    /// Assert a boolean condition with a given name.
    fn assert_named(
        &mut self,
        cond: smtlib::Bool<'st>,
        name: &'st str,
    ) -> Result<(), SmtBackendError> {
        let anno = self.st.alloc_slice(&[ast::Attribute::WithValue(
            Keyword(":named"),
            AttributeValue::Symbol(lexicon::Symbol(name)),
        )]);
        let assertion = self.st.alloc(ast::Term::Annotation(cond.term(), anno));
        let cmd = ast::Command::Assert(assertion);
        self.run_command(cmd).map(|_| ())
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

    /// Translate our IR `Term` into an smtlib `Dynamic`. `var_map` binds each
    /// quantified variable to a domain constant; grounding has eliminated all
    /// free variables by the time we reach here.
    fn translate_term(&self, term: &Term, var_map: &HashMap<VarId, ConstId>) -> Dynamic<'st> {
        match term {
            Term::Var(v) => self.smt_domain_consts[&var_map[v]],
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
    fn translate_atom(&self, atom: &Atom, var_map: &HashMap<VarId, ConstId>) -> smtlib::Bool<'st> {
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

    /// Ground a `Formula` against the loaded instance's finite domain into a
    /// quantifier-free smtlib `Bool`. Universal quantifiers become explicit
    /// conjunctions over their sort's domain; existentials become disjunctions.
    fn ground_formula(
        &self,
        formula: &Formula,
        var_map: &HashMap<VarId, ConstId>,
    ) -> smtlib::Bool<'st> {
        match formula {
            Formula::Atom(atom) => self.translate_atom(atom, var_map),
            Formula::And(fs) => {
                let bools: Vec<_> = fs.iter().map(|f| self.ground_formula(f, var_map)).collect();
                self.make_and(&bools)
            }
            Formula::Or(fs) => {
                let bools: Vec<_> = fs.iter().map(|f| self.ground_formula(f, var_map)).collect();
                self.make_or(&bools)
            }
            Formula::Not(f) => !self.ground_formula(f, var_map),
            Formula::Implies(lhs, rhs) => {
                let l = self.ground_formula(lhs, var_map);
                let r = self.ground_formula(rhs, var_map);
                l.implies(r)
            }
            Formula::Forall(vars, body) => {
                // Universal quantification cannot skip non-witness bindings, so
                // it must enumerate the full Cartesian product.
                let bools: Vec<_> = self
                    .cartesian_bindings(vars, var_map)
                    .into_iter()
                    .map(|m| self.ground_formula(body, &m))
                    .collect();
                self.make_and(&bools)
            }
            Formula::Exists(vars, body) => {
                // Existential witnesses only matter if the body could be true;
                // specialize the binding enumeration against any conjuncts
                // over ground-only predicates.
                let conjuncts = body_conjuncts(body);
                let bools: Vec<_> = self
                    .specialize_bindings(vars, &conjuncts, var_map.clone())
                    .into_iter()
                    .map(|m| self.ground_formula(body, &m))
                    .collect();
                self.make_or(&bools)
            }
        }
    }

    /// Ground an `Axiom` into a collection of quantifier-free smtlib `Bool`s,
    /// one per binding of the axiom's universal variables over the finite
    /// domain (specialized against ground-only body atoms where applicable).
    /// All instances should be gated on the same activator literal by the
    /// caller.
    fn ground_axiom(&self, axiom: &Axiom) -> Vec<smtlib::Bool<'st>> {
        let base: HashMap<VarId, ConstId> = HashMap::new();
        let var_maps = match axiom.body() {
            AxiomBody::Horn { body, .. } | AxiomBody::Integrity { body } => {
                let constraints: Vec<&Atom> = body.iter().collect();
                self.specialize_bindings(axiom.vars(), &constraints, base)
            }
            _ => self.cartesian_bindings(axiom.vars(), &base),
        };

        var_maps
            .into_iter()
            .map(|var_map| match axiom.body() {
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
                AxiomBody::General(formula) => self.ground_formula(formula, &var_map),
            })
            .collect()
    }

    /// Full Cartesian-product enumeration of `vars` over the finite domain,
    /// extending each base binding. Used when we have no body constraints to
    /// specialize on (universal quantifiers, functional facts).
    fn cartesian_bindings(
        &self,
        vars: &[(VarId, SortId)],
        base: &HashMap<VarId, ConstId>,
    ) -> Vec<HashMap<VarId, ConstId>> {
        enumerate_bindings(vars, &self.smt_domain)
            .into_iter()
            .map(|binding| {
                let mut m = base.clone();
                m.extend(binding);
                m
            })
            .collect()
    }

    /// Enumerate bindings of `vars` (extending `base`) that have a chance of
    /// satisfying every `constraint` atom which is over a *ground-only*
    /// predicate. Constraints over other predicates are ignored — those atoms
    /// remain in the SMT body and the solver evaluates them.
    ///
    /// This collapses the Cartesian product against the actual ground fact
    /// sets of closed-world ground-only predicates (e.g. `manages`, `fired`).
    /// For a rule like `manages_plus_step` with body `mp(x,z) ∧ manages(z,y)`,
    /// this turns an O(|domain|³) enumeration into O(#manages-facts · |domain|).
    fn specialize_bindings(
        &self,
        vars: &[(VarId, SortId)],
        constraints: &[&Atom],
        base: HashMap<VarId, ConstId>,
    ) -> Vec<HashMap<VarId, ConstId>> {
        let mut bound: HashSet<VarId> = base.keys().copied().collect();
        let mut bindings: Vec<HashMap<VarId, ConstId>> = vec![base];

        for atom in constraints {
            let Atom::Predicate { symbol, args } = atom else {
                continue;
            };
            if !self.ground_only_preds.contains(symbol) {
                continue;
            }
            let Some(facts) = self.ground_fact_index.get(symbol) else {
                // Closed-world ground-only predicate with no facts: the atom
                // is always false, so no binding can satisfy the body.
                return Vec::new();
            };

            bindings = bindings
                .into_iter()
                .flat_map(|b| {
                    facts
                        .iter()
                        .filter_map(move |fact| unify_atom(args, fact, &b))
                })
                .collect();

            for arg in args.iter() {
                if let Term::Var(v) = arg {
                    bound.insert(*v);
                }
            }

            if bindings.is_empty() {
                return bindings;
            }
        }

        let remaining: Vec<(VarId, SortId)> = vars
            .iter()
            .copied()
            .filter(|(v, _)| !bound.contains(v))
            .collect();

        if remaining.is_empty() {
            bindings
        } else {
            bindings
                .into_iter()
                .flat_map(|b| {
                    enumerate_bindings(&remaining, &self.smt_domain)
                        .into_iter()
                        .map(move |ext| {
                            let mut nb = b.clone();
                            nb.extend(ext);
                            nb
                        })
                })
                .collect()
        }
    }

    // -- Connective helpers -------------------------------------------------

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

/// Low-level helper to get an unsat core.
fn get_unsat_core<'st, B>(
    solver: &mut smtlib::Solver<'st, B>,
) -> Result<GetUnsatCoreResponse<'st>, smtlib::Error>
where
    B: smtlib::Backend,
{
    let cmd = ast::Command::GetUnsatCore;
    let resp = solver.run_command(cmd)?;
    if let GeneralResponse::SpecificSuccessResponse(
        SpecificSuccessResponse::GetUnsatCoreResponse(resp),
    ) = resp
    {
        Ok(resp)
    } else {
        unreachable!("wrong response from get-unsat-core");
    }
}

impl<'st, B: smtlib::Backend> Backend for SmtBackend<'st, B> {
    type Error = SmtBackendError;

    fn load_instance(&mut self, instance: &Instance<'_>) -> Result<(), Self::Error> {
        assert!(
            !self.loaded,
            "SmtBackend::load_instance called twice; use set_active_axioms for ablation"
        );
        trace!("loading instance");
        let theory = instance.theory();

        trace!("declaring sorts");
        // 1. Register sort descriptors (no solver command; sorts are declared
        //    implicitly when first used in declare_fun).
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
        // 2. Declare domain constants via declare_fun (0-arity).
        for (sort_id, constants) in instance.domain() {
            let sort = self.smt_sorts[sort_id];
            for &const_id in constants {
                let const_name = instance.constant(const_id).name();
                let fun = smtlib::funs::Fun::new(self.st, const_name, vec![], sort);
                self.solver.declare_fun(&fun)?;
                let name = self.st.alloc_str(const_name);
                let qi =
                    ast::QualIdentifier::Identifier(ast::Identifier::Simple(lexicon::Symbol(name)));
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

        // Snapshot the domain so grounding helpers can enumerate over it.
        self.smt_domain = instance.domain().clone();

        // Identify "ground-only" predicates and index their facts. A predicate
        // is ground-only iff it is closed-world and has no Horn rule producing
        // it — its truth set is then exactly the set of ground facts in the
        // instance. We use this both to specialize binding enumeration in
        // `ground_axiom` and to emit the CWA negations below.
        let horn_heads: HashSet<SymbolId> = theory
            .axioms()
            .filter_map(|(_, a)| match a.body() {
                AxiomBody::Horn {
                    head: Atom::Predicate { symbol, .. },
                    ..
                } => Some(*symbol),
                _ => None,
            })
            .collect();
        for (sym_id, decl) in theory.symbols() {
            let Some(sig) = decl.signature() else {
                continue;
            };
            if sig.closed_world() && sig.ret().is_none() && !horn_heads.contains(&sym_id) {
                self.ground_only_preds.insert(sym_id);
            }
        }
        for fact in instance.facts() {
            if let Atom::Predicate { symbol, args } = fact
                && self.ground_only_preds.contains(symbol)
                && let Some(tuple) = args
                    .iter()
                    .map(|t| match t {
                        Term::DomainConst(c) => Some(*c),
                        _ => None,
                    })
                    .collect::<Option<Vec<_>>>()
            {
                self.ground_fact_index
                    .entry(*symbol)
                    .or_default()
                    .push(tuple);
            }
        }

        let empty_var_map = HashMap::new();

        // 4. Assert per-sort distinctness. Coverage is no longer needed: with
        //    every axiom grounded over the finite domain there are no free
        //    SMT-level variables left, so cvc5 has no reason to invent
        //    phantom domain elements.
        trace!("asserting domain distinctness");
        for constants in instance.domain().values() {
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
        }

        // 5. Assert ground facts.
        trace!("asserting ground facts");
        for fact in instance.facts() {
            let b = self.translate_atom(fact, &empty_var_map);
            self.solver.assert(b)?;
        }

        // 6. Declare an activator boolean per theory axiom and assert one
        //    `(=> activator ground_instance)` per binding of the axiom's
        //    quantified variables over the finite domain. Toggling the
        //    activator turns the whole axiom on/off without re-asserting.
        trace!("grounding and asserting axioms");
        let bool_sort = smtlib::sorts::Sort::Static(smtlib::Bool::AST_SORT);
        let mut total_ground_clauses: usize = 0;
        for (axiom_id, axiom) in theory.axioms() {
            let act_name = self
                .st
                .alloc_str(&format!("_act_a{}", self.activator_names.len()));
            let fun = smtlib::funs::Fun::new(self.st, act_name, vec![], bool_sort);
            self.solver.declare_fun(&fun)?;
            self.activator_names.push((axiom_id, act_name));

            let act_qi =
                ast::QualIdentifier::Identifier(ast::Identifier::Simple(lexicon::Symbol(act_name)));
            let act_bool = self.to_bool(ast::Term::Identifier(act_qi));

            let instances = self.ground_axiom(axiom);
            total_ground_clauses += instances.len();
            for (i, ground) in instances.into_iter().enumerate() {
                let gac_name = self.st.alloc_str(&format!("{}_{i}", act_name));
                trace!("asserting ground axiom clause {}", gac_name);
                self.assert_named(act_bool.implies(ground), &gac_name)?;
                self.axiom_activators.insert(axiom_id, gac_name);
            }
        }
        trace!("asserted {} ground axiom clauses", total_ground_clauses);

        // 7. Pure-CWA negations for ground-only predicates: any tuple not
        //    asserted as a fact is asserted false. Unconditional (not gated
        //    on any axiom activator) because they encode instance state, not
        //    theory knowledge.
        trace!("asserting ground-only CWA negations");
        for &sym_id in &self.ground_only_preds {
            let sig = theory
                .symbol(sym_id)
                .signature()
                .expect("ground-only predicate must have a signature (added to set with one)");
            let facts: HashSet<&Vec<ConstId>> = self
                .ground_fact_index
                .get(&sym_id)
                .into_iter()
                .flatten()
                .collect();
            for tuple in enumerate_ground_tuples(sig.params(), instance.domain()) {
                if facts.contains(&tuple) {
                    continue;
                }
                let atom = Atom::Predicate {
                    symbol: sym_id,
                    args: tuple.into_iter().map(Term::DomainConst).collect(),
                };
                let b = self.translate_atom(&atom, &empty_var_map);
                self.solver.assert(!b)?;
            }
        }

        // For Horn-derived CWA predicates, the closure is enforced via the
        // auto-generated completion axioms (added by `finalize_completions`),
        // which flow through the activator-gating loop above and are thus
        // ablatable like any other implicit axiom.

        self.active_axioms = instance.active_axioms().clone();
        self.loaded = true;
        Ok(())
    }

    fn set_active_axioms(&mut self, instance: &Instance<'_>) -> Result<(), Self::Error> {
        debug_assert!(self.loaded, "set_active_axioms called before load_instance");
        let new_active = instance.active_axioms();
        debug_assert!(
            new_active.is_subset(&self.active_axioms),
            "monotone-ablation invariant violated: new active set must be a subset of the previous"
        );
        trace!(
            "set_active_axioms: {} axioms now active ({} dropped)",
            new_active.len(),
            self.active_axioms.len() - new_active.len(),
        );
        self.active_axioms = new_active.clone();
        Ok(())
    }

    fn check_entailment(&mut self, query: &Formula) -> Result<QueryResult, Self::Error> {
        trace!("starting entailment check");
        let q = self.ground_formula(query, &HashMap::new());
        let activator_pins = self.build_activator_pins();

        // T union F union {not q} unsat  =>  q is entailed.
        let (entailed, core) = self.solver.scope(|solver| {
            for pin in &activator_pins {
                solver.assert(*pin)?;
            }
            solver.assert(!q)?;
            let sat = solver.check_sat()?;
            let core = if sat == smtlib::SatResult::Unsat {
                Some(get_unsat_core(solver)?)
            } else {
                None
            };
            Ok((sat, core))
        })?;
        if entailed == smtlib::SatResult::Unsat {
            return Ok(QueryResult::Entailed {
                core: self.process_unsat_core(core.expect("unsat path must have core"))?,
            });
        }

        // T union F union {q} unsat  =>  not-q is entailed (q is refuted).
        let (refuted, core) = self.solver.scope(|solver| {
            for pin in &activator_pins {
                solver.assert(*pin)?;
            }
            solver.assert(q)?;
            let sat = solver.check_sat()?;
            let core = if sat == smtlib::SatResult::Unsat {
                Some(get_unsat_core(solver)?)
            } else {
                None
            };
            Ok((sat, core))
        })?;
        if refuted == smtlib::SatResult::Unsat {
            return Ok(QueryResult::Refuted {
                core: self.process_unsat_core(core.expect("unsat path must have core"))?,
            });
        }

        Ok(QueryResult::Undetermined)
    }

    fn recheck_entailment(
        &mut self,
        query: &Formula,
        expected: QueryResult,
    ) -> Result<QueryResult, Self::Error> {
        trace!(
            "starting directed entailment recheck (expected={:?})",
            expected
        );
        let q = self.ground_formula(query, &HashMap::new());
        let activator_pins = self.build_activator_pins();

        // Under monotone ablation the verdict can only stay at `expected` or
        // degrade to Undetermined. So we only need to check the one direction
        // that could flip: assert the *probe* (negation of the expected-witness
        // formula) and see if it's satisfiable.
        //
        //   expected = Entailed  ⇒ probe = ¬q;  sat ⇒ no longer entailed
        //   expected = Refuted   ⇒ probe =  q;  sat ⇒ no longer refuted
        let probe = match expected {
            QueryResult::Entailed { .. } => !q,
            QueryResult::Refuted { .. } => q,
            QueryResult::Undetermined => {
                panic!("recheck_entailment called with Undetermined expected")
            }
        };

        let res = self.solver.scope(|solver| {
            for pin in &activator_pins {
                solver.assert(*pin)?;
            }
            solver.assert(probe)?;
            solver.check_sat()
        })?;
        Ok(match res {
            smtlib::SatResult::Unsat => expected,
            _ => QueryResult::Undetermined,
        })
    }
}

impl<'st, B: smtlib::Backend> SmtBackend<'st, B> {
    fn build_activator_pins(&self) -> Vec<smtlib::Bool<'st>> {
        // Pin each activator literal positively or negatively for the current
        // active-axiom set.
        // (`check-sat-assuming` would be the natural fit, but smtlib 0.3.0's
        // `PropLiteral` Display impl is buggy and prints both variants
        // identically, so callers use plain bool asserts inside a push/pop
        // scope instead. Still much cheaper than re-translating the axioms
        // each step.)
        let mut pins = Vec::with_capacity(self.activator_names.len());
        for &(axiom_id, name) in &self.activator_names {
            let qi =
                ast::QualIdentifier::Identifier(ast::Identifier::Simple(lexicon::Symbol(name)));
            let act_bool = self.to_bool(ast::Term::Identifier(qi));
            if self.active_axioms.contains(&axiom_id) {
                pins.push(act_bool);
            } else {
                pins.push(!act_bool);
            }
        }
        pins
    }

    /// Convert a get-unsat-core response into a list of axiom IDs in the core.
    fn process_unsat_core(
        &self,
        core: GetUnsatCoreResponse<'_>,
    ) -> Result<Vec<AxiomId>, SmtBackendError> {
        let mut seen: HashSet<AxiomId> = HashSet::new();
        let mut result = Vec::with_capacity(core.0.len());
        for sym in core.0 {
            if let Some(&axiom_id) = self.axiom_activators.get_key(&sym.0)
                && seen.insert(axiom_id)
            {
                result.push(axiom_id);
            }
        }
        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::theories::{GroundModel, Theory};
    use smtlib::Storage;
    use smtlib::backend::cvc5_binary::Cvc5Binary;

    fn build_test_theory() -> Theory {
        theory! {
            sorts!(employee);
            predicates!(
                manages { (employee, employee) },
                can_fire { (employee, employee) },
                unrelated { (employee, employee) },
            );
            horn! {
                name:     "manages_can_fire",
                implicit: false,
                nl:       "managers can fire",
                forall (x: employee, y: employee) {
                    body: manages(x, y);
                    head: can_fire(x, y);
                }
            };
            horn! {
                name:     "unrelated_rule",
                implicit: false,
                nl:       "unrelated derivation",
                forall (x: employee, y: employee) {
                    body: manages(x, y);
                    head: unrelated(x, y);
                }
            };
            integrity! {
                name:     "no_self_fire",
                implicit: true,
                nl:       "no one fires themselves",
                forall (x: employee) {
                    body: can_fire(x, x);
                }
            };
        }
    }

    fn axiom_id_by_name(theory: &Theory, name: &str) -> AxiomId {
        theory
            .axioms()
            .find(|(_, a)| a.name() == name)
            .map(|(id, _)| id)
            .unwrap_or_else(|| panic!("axiom {name} not found"))
    }

    fn make_backend(st: &Storage) -> SmtBackend<'_, Cvc5Binary> {
        let cvc5 = Cvc5Binary::new("cvc5").expect("spawn cvc5");
        SmtBackend::new(st, cvc5).expect("construct backend")
    }

    #[test]
    fn entailed_core_contains_loadbearing_axiom() {
        let theory = build_test_theory();
        let employee = theory.find_sort("employee");
        let manages = theory.find_symbol("manages");
        let can_fire = theory.find_symbol("can_fire");

        let mut model = GroundModel::new(&theory);
        let alice = model.add_constant("alice", employee);
        let bob = model.add_constant("bob", employee);
        model.add_predicate_fact(manages, vec![alice, bob]);
        let instance = Instance::from_ground_model(model);

        let query = Formula::Atom(Atom::Predicate {
            symbol: can_fire,
            args: vec![Term::DomainConst(alice), Term::DomainConst(bob)],
        });

        let st = Storage::new();
        let mut backend = make_backend(&st);
        backend.load_instance(&instance).unwrap();
        let result = backend.check_entailment(&query).unwrap();

        let mcf = axiom_id_by_name(&theory, "manages_can_fire");
        let unrel = axiom_id_by_name(&theory, "unrelated_rule");
        match result {
            QueryResult::Entailed { core } => {
                assert!(
                    core.contains(&mcf),
                    "core missing manages_can_fire: {core:?}"
                );
                assert!(
                    !core.contains(&unrel),
                    "core unexpectedly contains unrelated_rule: {core:?}"
                );
            }
            other => panic!("expected Entailed, got {other:?}"),
        }
    }

    #[test]
    fn refuted_core_contains_integrity_axiom() {
        let theory = build_test_theory();
        let employee = theory.find_sort("employee");
        let manages = theory.find_symbol("manages");
        let can_fire = theory.find_symbol("can_fire");

        let mut model = GroundModel::new(&theory);
        let alice = model.add_constant("alice", employee);
        let bob = model.add_constant("bob", employee);
        // A fact so the domain isn't empty; irrelevant to the self-fire query.
        model.add_predicate_fact(manages, vec![alice, bob]);
        let instance = Instance::from_ground_model(model);

        let query = Formula::Atom(Atom::Predicate {
            symbol: can_fire,
            args: vec![Term::DomainConst(alice), Term::DomainConst(alice)],
        });

        let st = Storage::new();
        let mut backend = make_backend(&st);
        backend.load_instance(&instance).unwrap();
        let result = backend.check_entailment(&query).unwrap();

        let nsf = axiom_id_by_name(&theory, "no_self_fire");
        match result {
            QueryResult::Refuted { core } => {
                assert!(core.contains(&nsf), "core missing no_self_fire: {core:?}");
            }
            other => panic!("expected Refuted, got {other:?}"),
        }
    }

    #[test]
    fn deactivating_core_axioms_degrades_verdict() {
        let theory = build_test_theory();
        let employee = theory.find_sort("employee");
        let manages = theory.find_symbol("manages");
        let can_fire = theory.find_symbol("can_fire");

        let mut model = GroundModel::new(&theory);
        let alice = model.add_constant("alice", employee);
        let bob = model.add_constant("bob", employee);
        model.add_predicate_fact(manages, vec![alice, bob]);
        let mut instance = Instance::from_ground_model(model);

        let query = Formula::Atom(Atom::Predicate {
            symbol: can_fire,
            args: vec![Term::DomainConst(alice), Term::DomainConst(bob)],
        });

        let st = Storage::new();
        let mut backend = make_backend(&st);
        backend.load_instance(&instance).unwrap();
        let initial = backend.check_entailment(&query).unwrap();
        let core = match &initial {
            QueryResult::Entailed { core } => core.clone(),
            other => panic!("expected Entailed initially, got {other:?}"),
        };
        assert!(!core.is_empty(), "entailed core must be non-empty");

        for id in &core {
            instance.deactivate_axiom(*id);
        }
        backend.set_active_axioms(&instance).unwrap();
        let after = backend.recheck_entailment(&query, initial.clone()).unwrap();
        assert_eq!(after, QueryResult::Undetermined);
    }
}
