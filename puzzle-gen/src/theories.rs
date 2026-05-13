//! Representation of a first-order theory (schema) with implicit axioms. This
//! framework allows building up a general theory which can be instantiated with
//! different models.

use std::{
    collections::{HashMap, HashSet},
    fmt::Display,
    ops::ControlFlow,
};

use itertools::{Either, Itertools};
use log::debug;
use rand::{Rng, seq::SliceRandom};
use slotmap::{SlotMap, new_key_type};

new_key_type! {
    /// Identifiers for sorts
    pub struct SortId;

    /// Identifiers for function symbols
    pub struct SymbolId;

    /// Identifiers for axioms
    pub struct AxiomId;

    /// Identifiers for domain constants in a `GroundModel` / `Instance`.
    ///
    /// Distinct from `SymbolId` so the keyspace of theory-declared symbols
    /// (sorts, predicates, functions, theory-level constants) cannot be
    /// accidentally mixed with the keyspace of model domain elements.
    pub struct ConstId;
}

/// Declaration of a domain constant: its (display) name and the sort it
/// inhabits.
#[derive(Debug, Clone)]
pub struct ConstDecl {
    /// Stable name of this constant, for instance for use by SMT solvers
    name: String,
    sort: SortId,
}

impl ConstDecl {
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn sort(&self) -> SortId {
        self.sort
    }
}

/// Identifiers for variables
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VarId(pub u32);

/// Sort declaration associating a sort with its domain.
#[derive(Debug, Clone)]
pub struct SortDecl {
    id: SortId,
    name: String,
}

impl SortDecl {
    pub fn name(&self) -> &str {
        &self.name
    }
}

/// Symbol declaration, denotes a symbol in a ranked alphabet. That is, each
/// symbol can have multiple "child" symbols, with a fixed number per symbol.
#[derive(Debug, Clone)]
pub struct SymbolDecl {
    id: SymbolId,
    name: String,
    signature: Option<Signature>,
    /// Template used to render an application of this symbol in natural
    /// language. Positional placeholders `{0}`, `{1}`, ... refer to the
    /// argument names; `{ret}` refers to the return value (functions only).
    nl_template: Option<String>,
}

impl SymbolDecl {
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn signature(&self) -> Option<&Signature> {
        self.signature.as_ref()
    }

    pub fn nl_template(&self) -> Option<&str> {
        self.nl_template.as_deref()
    }
}

/// Signature for a function symbol
#[derive(Debug, Clone)]
pub struct Signature {
    params: Vec<SortId>,
    ret: Option<SortId>,
    /// Closed-world annotation for predicates. When true, the theory builder
    /// auto-generates a Clark-completion axiom (implicit) for this predicate
    /// during `finalize_completions`. Always false for functions.
    closed_world: bool,
}

impl Signature {
    /// Construct a new predicate signature.
    fn new_predicate(params: Vec<SortId>, closed_world: bool) -> Self {
        Self {
            params,
            ret: None,
            closed_world,
        }
    }

    /// Construct a new function signature.
    fn new_function(params: Vec<SortId>, ret: SortId) -> Self {
        Self {
            params,
            ret: Some(ret),
            closed_world: false,
        }
    }

    pub fn params(&self) -> &[SortId] {
        &self.params
    }

    pub fn ret(&self) -> Option<SortId> {
        self.ret
    }

    pub fn closed_world(&self) -> bool {
        self.closed_world
    }
}

#[derive(Debug, Clone)]
pub enum Term {
    /// Variable reference
    Var(VarId),
    /// Theory-level constant (declared in the `Theory` itself).
    Const(SymbolId),
    /// Domain constant from a `GroundModel` / `Instance`.
    DomainConst(ConstId),
    /// Function application for n-ary functions.
    App { symbol: SymbolId, args: Vec<Term> },
}

/// An atom is a predicate applied to terms, or equality/disequality.
/// Kept separate from Term because atoms return Bool and have special structure
/// (they're the things that appear in rule bodies and heads).
#[derive(Clone, Debug)]
pub enum Atom {
    Predicate { symbol: SymbolId, args: Vec<Term> },
    Eq(Term, Term),
    Neq(Term, Term),
}

#[derive(Clone, Debug)]
pub enum Formula {
    Atom(Atom),
    And(Vec<Formula>),
    Or(Vec<Formula>),
    Not(Box<Formula>),
    Implies(Box<Formula>, Box<Formula>),
    Forall(Vec<(VarId, SortId)>, Box<Formula>),
    Exists(Vec<(VarId, SortId)>, Box<Formula>),
}

#[derive(Clone, Debug)]
pub enum AxiomBody {
    /// Horn clauses: conjoined body clauses imply head.
    Horn {
        body: Vec<Atom>,
        head: Atom,
    },
    /// Integrity rules: negation of the conjunction of body atoms
    Integrity {
        body: Vec<Atom>,
    },
    /// Function definition: maps particular inputs to the given output
    FunctionalFact {
        symbol: SymbolId,
        args: Vec<Term>,
        value: Term,
    },
    General(Formula),
}

#[derive(Clone, Debug)]
pub struct Axiom {
    id: AxiomId,
    meta: AxiomMeta,
    /// Bound variables with their sorts. For Horn/Integrity bodies these are
    /// the implicitly universally-quantified variables; for General bodies this
    /// list may be empty (the formula carries its own quantifiers).
    vars: Vec<(VarId, SortId)>,
    body: AxiomBody,
}

impl Axiom {
    pub fn id(&self) -> AxiomId {
        self.id
    }

    pub fn name(&self) -> &str {
        self.meta.name()
    }

    pub fn kind(&self) -> &AxiomKind {
        &self.meta.kind
    }

    /// Convenience function to check if this axiom is implicit.
    pub fn implicit_by_default(&self) -> bool {
        self.meta.implicit_by_default()
    }

    pub fn vars(&self) -> &[(VarId, SortId)] {
        &self.vars
    }

    pub fn body(&self) -> &AxiomBody {
        &self.body
    }

    pub fn natural_language(&self) -> Option<&str> {
        self.meta.natural_language()
    }
}

/// Axiom kind, determines whether it is an "implicit" (i.e. recoverable from a
/// world model) or "explicit" axiom.
#[derive(Clone, Debug)]
pub enum AxiomKind {
    Implicit,
    Explicit,
}

impl AxiomKind {
    /// Check if this axiom is implicit.
    pub fn is_implicit(&self) -> bool {
        matches!(self, AxiomKind::Implicit)
    }
}

impl Display for AxiomKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                AxiomKind::Implicit => "implicit",
                AxiomKind::Explicit => "explicit",
            }
        )
    }
}

#[derive(Clone, Debug)]
pub struct AxiomMeta {
    name: String,
    kind: AxiomKind,
    natural_language: Option<String>,
    depends_on: Vec<AxiomId>,
}

impl AxiomMeta {
    /// Create a new "raw" axiom (without natural language description)
    pub fn new_raw(name: impl Into<String>, kind: AxiomKind, depends_on: Vec<AxiomId>) -> Self {
        Self {
            name: name.into(),
            kind,
            natural_language: None,
            depends_on,
        }
    }

    /// Create a new axiom with a natural language description
    pub fn new_nl(
        name: impl Into<String>,
        kind: AxiomKind,
        natural_language: impl Into<String>,
        depends_on: Vec<AxiomId>,
    ) -> Self {
        Self {
            name: name.into(),
            kind,
            natural_language: Some(natural_language.into()),
            depends_on,
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn natural_language(&self) -> Option<&str> {
        self.natural_language.as_deref()
    }

    pub fn implicit_by_default(&self) -> bool {
        self.kind.is_implicit()
    }
}

/// A theory schema: sorts and symbols declared, axioms defined parametrically.
/// Becomes an Instance when sorts are grounded and facts are added.
pub struct Theory {
    sorts: SlotMap<SortId, SortDecl>,
    symbols: SlotMap<SymbolId, SymbolDecl>,
    axioms: SlotMap<AxiomId, Axiom>,
    /// Natural language preamble to include in the system prompt for the
    /// natural langauge rendering.
    nl_preamble: Option<String>,
}

impl Theory {
    pub fn sorts(&self) -> slotmap::basic::Iter<'_, SortId, SortDecl> {
        self.sorts.iter()
    }

    pub fn sort(&self, id: SortId) -> &SortDecl {
        &self.sorts[id]
    }

    /// Locate the sort ID for a given sort name
    pub fn find_sort(&self, name: &str) -> SortId {
        self.sorts
            .iter()
            .find(|(_, s)| s.name() == name)
            .map(|(id, _)| id)
            .unwrap_or_else(|| panic!("No such sort {name}"))
    }

    /// Locate the symbol ID for a given symbol name
    pub fn find_symbol(&self, name: &str) -> SymbolId {
        self.symbols
            .iter()
            .find(|(_, s)| s.name() == name)
            .map(|(id, _)| id)
            .unwrap_or_else(|| panic!("No such sort {name}"))
    }

    pub fn symbols(&self) -> slotmap::basic::Iter<'_, SymbolId, SymbolDecl> {
        self.symbols.iter()
    }

    pub fn symbol(&self, id: SymbolId) -> &SymbolDecl {
        &self.symbols[id]
    }

    pub fn axioms(&self) -> slotmap::basic::Iter<'_, AxiomId, Axiom> {
        self.axioms.iter()
    }

    pub fn axiom(&self, id: AxiomId) -> &Axiom {
        &self.axioms[id]
    }

    /// Construct a new empty theory.
    pub fn new() -> Self {
        debug!("creating new empty theory");
        Self {
            sorts: SlotMap::with_key(),
            symbols: SlotMap::with_key(),
            axioms: SlotMap::with_key(),
            nl_preamble: None,
        }
    }

    /// Set the natural-language preamble for this theory. This is used when
    /// generating the natural language problems to give instructions to the LLM
    /// on how to generate e.g. names, context, etc.
    pub fn set_preamble(&mut self, preamble: impl Into<String>) {
        self.nl_preamble = Some(preamble.into())
    }

    /// Add a sort to the theory.
    pub fn declare_sort(&mut self, name: impl Into<String>) -> SortId {
        self.sorts.insert_with_key(|id| SortDecl {
            id,
            name: name.into(),
        })
    }

    /// Add a  predicate to the theory.
    pub fn declare_predicate<I>(
        &mut self,
        name: impl Into<String>,
        params: Vec<SortId>,
        nl_template: Option<I>,
        closed_world: bool,
    ) -> SymbolId
    where
        I: Into<String>,
    {
        self.symbols.insert_with_key(|id| SymbolDecl {
            id,
            name: name.into(),
            signature: Some(Signature::new_predicate(params, closed_world)),
            nl_template: nl_template.map(|t| t.into()),
        })
    }

    /// Add a function to the theory.
    pub fn declare_function<I>(
        &mut self,
        name: impl Into<String>,
        params: Vec<SortId>,
        result: SortId,
        nl_template: Option<I>,
    ) -> SymbolId
    where
        I: Into<String>,
    {
        self.symbols.insert_with_key(|id| SymbolDecl {
            id,
            name: name.into(),
            signature: Some(Signature::new_function(params, result)),
            nl_template: nl_template.map(|t| t.into()),
        })
    }

    /// Declare a constant symbol (0-ary, no signature).
    pub fn declare_constant(&mut self, name: impl Into<String>) -> SymbolId {
        self.symbols.insert_with_key(|id| SymbolDecl {
            id,
            name: name.into(),
            signature: None,
            nl_template: None,
        })
    }

    /// Add an axiom to the theory.
    pub fn add_axiom(
        &mut self,
        meta: AxiomMeta,
        vars: Vec<(VarId, SortId)>,
        body: AxiomBody,
    ) -> AxiomId {
        self.axioms.insert_with_key(|id| Axiom {
            id,
            meta,
            vars,
            body,
        })
    }

    /// Generate Clark-completion axioms for every predicate marked
    /// `closed_world`. Each completion is `∀args. P(args) → ⋁_rule body_rule`,
    /// where the bodies come from the Horn rules whose head is `P`. The
    /// completion is added as an implicit axiom, so it can be ablated like
    /// any other and falling back to open-world reasoning for `P`.
    ///
    /// Call once, after all predicates and Horn rules have been declared.
    pub fn finalize_completions(&mut self) {
        let cwa_predicates: Vec<(SymbolId, Vec<SortId>)> = self
            .symbols
            .iter()
            .filter_map(|(id, decl)| {
                decl.signature().and_then(|s| {
                    if s.closed_world() && s.ret().is_none() {
                        Some((id, s.params().to_vec()))
                    } else {
                        None
                    }
                })
            })
            .collect();

        for (head_sym, params) in cwa_predicates {
            let has_horn = self.axioms.iter().any(|(_, a)| {
                matches!(
                    a.body(),
                    AxiomBody::Horn { head: Atom::Predicate { symbol, .. }, .. }
                        if *symbol == head_sym
                )
            });
            if has_horn {
                self.add_completion_axiom(head_sym, &params);
            }
            // CWA-flagged predicates with no Horn rules are handled at
            // instance-load time by the SMT backend (which asserts negations
            // for non-fact ground tuples). No theory-level completion needed
            // — the ground facts ARE the predicate's definition.
        }
    }

    fn add_completion_axiom(&mut self, head_sym: SymbolId, params: &[SortId]) {
        let mut next_var: u32 = 0;
        let mut fresh = || {
            let v = VarId(next_var);
            next_var += 1;
            v
        };

        let arg_binders: Vec<(VarId, SortId)> = params.iter().map(|&s| (fresh(), s)).collect();
        let arg_vars: Vec<VarId> = arg_binders.iter().map(|(v, _)| *v).collect();

        // Collect Horn rules with this head; clone fields to avoid aliasing
        // self.axioms while we mutate below.
        let horn_rules: Vec<(Vec<(VarId, SortId)>, Vec<Atom>, Vec<Term>)> = self
            .axioms
            .iter()
            .filter_map(|(_, axiom)| match axiom.body() {
                AxiomBody::Horn {
                    body,
                    head: Atom::Predicate { symbol, args },
                } if *symbol == head_sym => {
                    Some((axiom.vars().to_vec(), body.clone(), args.clone()))
                }
                _ => None,
            })
            .collect();

        let mut disjuncts: Vec<Formula> = Vec::with_capacity(horn_rules.len());
        for (rule_vars, body, head_args) in horn_rules {
            // Build a rename map: rule's VarIds → fresh completion-scope VarIds.
            // Where the head puts a rule var in position i, prefer to map that
            // var directly to arg_vars[i]. Non-var head positions become Eq
            // atoms in the disjunct body.
            let mut rename: HashMap<VarId, VarId> = HashMap::new();
            let mut extra_eqs: Vec<Atom> = Vec::new();
            for (i, t) in head_args.iter().enumerate() {
                let arg_v = arg_vars[i];
                match t {
                    Term::Var(v) => match rename.get(v) {
                        // Repeated head var (e.g. P(x, x)) — bind to first
                        // and force the second slot equal.
                        Some(&prior) => {
                            extra_eqs.push(Atom::Eq(Term::Var(prior), Term::Var(arg_v)));
                        }
                        None => {
                            rename.insert(*v, arg_v);
                        }
                    },
                    other => {
                        extra_eqs.push(Atom::Eq(other.clone(), Term::Var(arg_v)));
                    }
                }
            }

            // Any rule var not unified with a head arg becomes a fresh
            // existentially-quantified variable in the disjunct.
            let mut existentials: Vec<(VarId, SortId)> = Vec::new();
            for &(v, s) in &rule_vars {
                if let std::collections::hash_map::Entry::Vacant(e) = rename.entry(v) {
                    let nv = fresh();
                    e.insert(nv);
                    existentials.push((nv, s));
                }
            }

            let rename_term = |t: &Term| -> Term {
                match t {
                    Term::Var(v) => Term::Var(*rename.get(v).unwrap_or(v)),
                    other => other.clone(),
                }
            };
            let rename_atom = |a: &Atom| -> Atom {
                match a {
                    Atom::Predicate { symbol, args } => Atom::Predicate {
                        symbol: *symbol,
                        args: args.iter().map(&rename_term).collect(),
                    },
                    Atom::Eq(l, r) => Atom::Eq(rename_term(l), rename_term(r)),
                    Atom::Neq(l, r) => Atom::Neq(rename_term(l), rename_term(r)),
                }
            };

            let mut conjuncts: Vec<Formula> =
                body.iter().map(|a| Formula::Atom(rename_atom(a))).collect();
            for eq in &extra_eqs {
                conjuncts.push(Formula::Atom(rename_atom(eq)));
            }

            let conj = match conjuncts.len() {
                1 => conjuncts.into_iter().next().unwrap(),
                _ => Formula::And(conjuncts),
            };
            let disjunct = if existentials.is_empty() {
                conj
            } else {
                Formula::Exists(existentials, Box::new(conj))
            };
            disjuncts.push(disjunct);
        }

        let head_atom = Formula::Atom(Atom::Predicate {
            symbol: head_sym,
            args: arg_vars.iter().copied().map(Term::Var).collect(),
        });

        // Empty disjunction means "no rule can derive P"; the completion
        // becomes `∀args. ¬P(args)`.
        let body = if disjuncts.is_empty() {
            Formula::Forall(
                arg_binders.clone(),
                Box::new(Formula::Not(Box::new(head_atom))),
            )
        } else {
            let rhs = if disjuncts.len() == 1 {
                disjuncts.into_iter().next().unwrap()
            } else {
                Formula::Or(disjuncts)
            };
            Formula::Forall(
                arg_binders.clone(),
                Box::new(Formula::Implies(Box::new(head_atom), Box::new(rhs))),
            )
        };

        let pred_name = self.symbols[head_sym].name().to_string();
        let name = format!("completion_{pred_name}");
        // Note that here we *don't* explicitly list a natural language rule for
        // the completion. First, it is awkward to state, and second, since it's
        // implicit, we are unconditionally "ablating" it by not including it in
        // the natural language rule listing.
        let meta = AxiomMeta::new_raw(name, AxiomKind::Implicit, vec![]);
        // `vars` left empty: the formula carries its own quantifiers.
        self.add_axiom(meta, vec![], AxiomBody::General(body));
    }
}

// -- Least Fixed Point helpers -----------------------------------------------

pub(crate) fn eval_term(term: &Term, binding: &HashMap<VarId, ConstId>) -> Option<ConstId> {
    match term {
        Term::DomainConst(c) => Some(*c),
        Term::Var(v) => binding.get(v).copied(),
        Term::Const(_) | Term::App { .. } => None,
    }
}

pub(crate) fn body_holds(
    body: &[Atom],
    binding: &HashMap<VarId, ConstId>,
    lfp: &HashSet<(SymbolId, Vec<ConstId>)>,
) -> bool {
    body.iter().all(|atom| match atom {
        Atom::Predicate { symbol, args } => args
            .iter()
            .map(|t| eval_term(t, binding))
            .collect::<Option<Vec<_>>>()
            .is_some_and(|gs| lfp.contains(&(*symbol, gs))),
        Atom::Eq(t1, t2) => matches!(
            (eval_term(t1, binding), eval_term(t2, binding)),
            (Some(a), Some(b)) if a == b
        ),
        Atom::Neq(t1, t2) => matches!(
            (eval_term(t1, binding), eval_term(t2, binding)),
            (Some(a), Some(b)) if a != b
        ),
    })
}

pub(crate) fn enumerate_bindings(
    vars: &[(VarId, SortId)],
    domain: &HashMap<SortId, Vec<ConstId>>,
) -> Vec<HashMap<VarId, ConstId>> {
    vars.iter().fold(vec![HashMap::new()], |acc, &(var, sort)| {
        let consts = domain.get(&sort).map_or(&[] as &[ConstId], Vec::as_slice);
        acc.into_iter()
            .flat_map(|b| {
                consts.iter().map(move |&c| {
                    let mut b = b.clone();
                    b.insert(var, c);
                    b
                })
            })
            .collect()
    })
}

/// A ground-truth model of a theory: the theory schema plus a concrete domain
/// of constants and the extensions of each predicate / function.
///
/// `GroundModel` borrows the theory it interprets, so all `SortId` and
/// `SymbolId` values used in the maps below refer to the same theory's arenas
/// — there is no separate keyspace to reconcile.
pub struct GroundModel<'t> {
    theory: &'t Theory,
    constants: SlotMap<ConstId, ConstDecl>,
    domain: HashMap<SortId, Vec<ConstId>>,
    predicates: HashMap<SymbolId, HashSet<Vec<ConstId>>>,
    functions: HashMap<SymbolId, HashMap<Vec<ConstId>, ConstId>>,
}

impl<'t> GroundModel<'t> {
    pub fn new(theory: &'t Theory) -> Self {
        Self {
            theory,
            constants: SlotMap::with_key(),
            domain: HashMap::new(),
            predicates: HashMap::new(),
            functions: HashMap::new(),
        }
    }

    pub fn theory(&self) -> &'t Theory {
        self.theory
    }

    pub fn constants(&self) -> &SlotMap<ConstId, ConstDecl> {
        &self.constants
    }

    pub fn constant(&self, id: ConstId) -> &ConstDecl {
        &self.constants[id]
    }

    pub fn domain(&self) -> &HashMap<SortId, Vec<ConstId>> {
        &self.domain
    }

    pub fn predicates(&self) -> &HashMap<SymbolId, HashSet<Vec<ConstId>>> {
        &self.predicates
    }

    pub fn functions(&self) -> &HashMap<SymbolId, HashMap<Vec<ConstId>, ConstId>> {
        &self.functions
    }

    /// Add a domain constant of the given sort and return its `ConstId`.
    pub fn add_constant(&mut self, name: impl Into<String>, sort: SortId) -> ConstId {
        let id = self.constants.insert(ConstDecl {
            name: name.into(),
            sort,
        });
        self.domain.entry(sort).or_default().push(id);
        id
    }

    /// Record a ground predicate fact `p(args)`.
    pub fn add_predicate_fact(&mut self, predicate: SymbolId, args: Vec<ConstId>) {
        self.predicates.entry(predicate).or_default().insert(args);
    }

    /// Record a ground function fact `f(args) = value`.
    pub fn add_function_fact(&mut self, function: SymbolId, args: Vec<ConstId>, value: ConstId) {
        self.functions
            .entry(function)
            .or_default()
            .insert(args, value);
    }

    /// Compute the LFP of all theory Horn axioms over this model's domain.
    ///
    /// Seeds from the explicit predicate facts and forward-chains until no new
    /// atoms are derived. Returns the full set of entailed ground predicate atoms.
    pub fn entailed_predicates(&self) -> HashSet<(SymbolId, Vec<ConstId>)> {
        let mut lfp: HashSet<(SymbolId, Vec<ConstId>)> = self
            .predicates
            .iter()
            .flat_map(|(&sym, tuples)| tuples.iter().map(move |t| (sym, t.clone())))
            .collect();

        loop {
            let mut added = false;
            for (_, axiom) in self.theory.axioms() {
                if let AxiomBody::Horn { body, head } = axiom.body()
                    && let Atom::Predicate {
                        symbol: head_sym,
                        args: head_args,
                    } = head
                {
                    for binding in enumerate_bindings(axiom.vars(), &self.domain) {
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
}

/// An instantiated theory: a `GroundModel` materialised as ground `Atom` facts,
/// plus an ablatable axiom set.
///
/// Constructed from a `GroundModel` via [`Instance::from_ground_model`] so that
/// the theory reference and the domain constant registry are shared by
/// construction.
pub struct Instance<'t> {
    theory: &'t Theory,
    constants: SlotMap<ConstId, ConstDecl>,
    domain: HashMap<SortId, Vec<ConstId>>,
    facts: Vec<Atom>,
    active_axioms: HashSet<AxiomId>,
}

impl<'t> Instance<'t> {
    /// Materialise a `GroundModel` into an `Instance` with all axioms active.
    ///
    /// Predicate extensions become `Atom::Predicate` facts; function
    /// extensions become `Atom::Eq(App(f, args), value)` facts.
    pub fn from_ground_model(model: GroundModel<'t>) -> Self {
        let GroundModel {
            theory,
            constants,
            domain,
            predicates,
            functions,
        } = model;

        let mut facts = Vec::new();
        for (symbol, tuples) in &predicates {
            for args in tuples {
                facts.push(Atom::Predicate {
                    symbol: *symbol,
                    args: args.iter().map(|c| Term::DomainConst(*c)).collect(),
                });
            }
        }
        for (symbol, map) in &functions {
            for (args, value) in map {
                facts.push(Atom::Eq(
                    Term::App {
                        symbol: *symbol,
                        args: args.iter().map(|c| Term::DomainConst(*c)).collect(),
                    },
                    Term::DomainConst(*value),
                ));
            }
        }

        let active_axioms = theory.axioms.iter().map(|(id, _)| id).collect();

        Self {
            theory,
            constants,
            domain,
            facts,
            active_axioms,
        }
    }

    pub fn theory(&self) -> &'t Theory {
        self.theory
    }

    pub fn constants(&self) -> &SlotMap<ConstId, ConstDecl> {
        &self.constants
    }

    pub fn constant(&self, id: ConstId) -> &ConstDecl {
        &self.constants[id]
    }

    pub fn domain(&self) -> &HashMap<SortId, Vec<ConstId>> {
        &self.domain
    }

    pub fn facts(&self) -> &[Atom] {
        &self.facts
    }

    pub fn active_axioms(&self) -> &HashSet<AxiomId> {
        &self.active_axioms
    }

    /// Deactivate an axiom (for ablation).
    pub fn deactivate_axiom(&mut self, id: AxiomId) {
        self.active_axioms.remove(&id);
        let ax = self.theory.axiom(id);
        debug!("deactivated axiom {} [{}]", ax.name(), ax.kind());
    }

    /// Get the natural language preamble of this instance.
    pub fn preamble(&self) -> Option<&str> {
        self.theory.nl_preamble.as_deref()
    }
}

/// Strategies for ablating axioms from theories during puzzle generation.
pub trait AblationStrategy {
    /// Perform a single ablation step. If ablation can continue, return `ControlFlow::Continue`.
    /// If ablation is done, return `ControlFlow::Break`.
    fn ablate(&mut self, theory: &mut Instance) -> ControlFlow<()>;
}

/// Ablate all implicit by default axioms at once.
pub struct AllAtOnceAblation;
impl AblationStrategy for AllAtOnceAblation {
    fn ablate(&mut self, inst: &mut Instance) -> ControlFlow<()> {
        for (id, axiom) in inst.theory.axioms() {
            if axiom.implicit_by_default() {
                inst.deactivate_axiom(id);
            }
        }
        ControlFlow::Break(())
    }
}

/// Randomly ablate implicit axioms one-at-a-time.
pub struct StochasticAblation {
    implicit_axioms_remaining: Vec<AxiomId>,
    explicit_axioms: Vec<AxiomId>,
}

impl StochasticAblation {
    pub fn new(theory: &Theory, rng: &mut impl Rng) -> Self {
        let (mut implicit_axioms_remaining, mut explicit_axioms): (Vec<AxiomId>, Vec<AxiomId>) =
            theory.axioms().partition_map(|(id, axiom)| {
                if axiom.implicit_by_default() {
                    Either::Left(id)
                } else {
                    Either::Right(id)
                }
            });
        implicit_axioms_remaining.shuffle(rng);
        explicit_axioms.shuffle(rng);
        Self {
            implicit_axioms_remaining,
            explicit_axioms,
        }
    }
}

impl AblationStrategy for StochasticAblation {
    fn ablate(&mut self, inst: &mut Instance) -> ControlFlow<()> {
        // Deactivate the implicit axioms first. If they're all gone, start
        // removing explicit axioms until we break the puzzle.
        let ax = self
            .implicit_axioms_remaining
            .pop()
            .or_else(|| self.explicit_axioms.pop());
        if let Some(ax) = ax {
            inst.deactivate_axiom(ax);
            ControlFlow::Continue(())
        } else {
            ControlFlow::Break(())
        }
    }
}

/// Interface for generating models of a given theory.
pub trait ModelGenerator<'t> {
    fn generate(&mut self) -> GroundModel<'t>;
}

/// Interface for generating queries against a given ground model.
///
/// The query is a `Formula` whose entailment under the model's theory will be
/// tested by the puzzle-generation loop. Implementations should pick queries
/// that exercise the *implicit* axioms of the theory; otherwise ablation will
/// not change the entailment status and the puzzle will not be interesting.
pub trait QueryGenerator<'t> {
    fn generate(&mut self, model: &GroundModel<'t>) -> Formula;
}

#[cfg(test)]
mod tests {
    /// Smoke-test: build a small workplace theory using the macros and check
    /// that all axiom variants round-trip through the Theory.
    #[test]
    fn macro_theory_construction() {
        let t = theory! {
            sorts!(employee, department);

            predicates!(
                manages { (employee, employee), nl: "{0} manages {1}" },
                can_fire { (employee, employee) },
                reports_to { (employee, employee), nl: "{0} reports to {1}" },
            );

            functions!(
                works_in { (employee) -> department, nl: "{0} works in {ret}" },
            );

            constants!(alice, bob, engineering);

            horn! {
                name:     "manages_can_fire",
                implicit: false,
                nl:       "Managers can fire their direct reports",
                forall (x: employee, y: employee) {
                    body: manages(x, y);
                    head: can_fire(x, y);
                }
            };

            horn! {
                name:     "manages_reports_to",
                implicit: true,
                nl:       "If X manages Y then Y reports to X",
                forall (x: employee, y: employee) {
                    body: manages(x, y);
                    head: reports_to(y, x);
                }
            };

            integrity! {
                name:     "no_self_manage",
                implicit: true,
                nl:       "Nobody manages themselves",
                forall (x: employee) {
                    body: manages(x, x);
                }
            };
        };

        // Verify sorts, symbols, and axioms were registered.
        assert_eq!(t.sorts().count(), 2);
        // 3 predicates + 1 function + 3 constants
        assert_eq!(t.symbols().count(), 7);
        assert_eq!(t.axioms().count(), 3);

        // Check axiom metadata round-trips.
        let names: Vec<&str> = t.axioms().map(|(_, a)| a.name()).collect();
        assert!(names.contains(&"manages_can_fire"));
        assert!(names.contains(&"manages_reports_to"));
        assert!(names.contains(&"no_self_manage"));

        // implicit_by_default flags
        let implicit_count = t.axioms().filter(|(_, a)| a.implicit_by_default()).count();
        assert_eq!(implicit_count, 2);
    }
}
