//! Representation of a first-order theory (schema) with implicit axioms. This
//! framework allows building up a general theory which can be instantiated with
//! different models.

use log::info;
use std::collections::{HashMap, HashSet};
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

/// Domain of a sort
#[derive(Debug, Clone)]
pub enum SortDomain {
    /// Uninterpreted domain, instantiated at compile time
    Uninterpreted,
    /// Explicitly enumerated sort with finite domain
    Enumerated(Vec<SymbolId>),
}

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
}

impl SymbolDecl {
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn signature(&self) -> Option<&Signature> {
        self.signature.as_ref()
    }
}

/// Signature for a function symbol
#[derive(Debug, Clone)]
pub struct Signature {
    params: Vec<SortId>,
    ret: Option<SortId>,
}

impl Signature {
    /// Construct a new predicate signature.
    fn new_predicate(params: Vec<SortId>) -> Self {
        Self { params, ret: None }
    }

    /// Construct a new function signature.
    fn new_function(params: Vec<SortId>, ret: SortId) -> Self {
        Self {
            params,
            ret: Some(ret),
        }
    }

    pub fn params(&self) -> &[SortId] {
        &self.params
    }

    pub fn ret(&self) -> Option<SortId> {
        self.ret
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

    pub fn implicit_by_default(&self) -> bool {
        self.meta.implicit_by_default()
    }

    pub fn natural_language(&self) -> &str {
        self.meta.natural_language()
    }

    pub fn depends_on(&self) -> &[AxiomId] {
        self.meta.depends_on()
    }

    pub fn vars(&self) -> &[(VarId, SortId)] {
        &self.vars
    }

    pub fn body(&self) -> &AxiomBody {
        &self.body
    }
}

#[derive(Clone, Debug)]
pub struct AxiomMeta {
    name: String,
    implicit_by_default: bool,
    natural_language: String,
    depends_on: Vec<AxiomId>,
}

impl AxiomMeta {
    pub fn new(
        name: impl Into<String>,
        implicit_by_default: bool,
        natural_language: impl Into<String>,
        depends_on: Vec<AxiomId>,
    ) -> Self {
        Self {
            name: name.into(),
            implicit_by_default,
            natural_language: natural_language.into(),
            depends_on,
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn implicit_by_default(&self) -> bool {
        self.implicit_by_default
    }

    pub fn natural_language(&self) -> &str {
        &self.natural_language
    }

    pub fn depends_on(&self) -> &[AxiomId] {
        &self.depends_on
    }
}

/// A theory schema: sorts and symbols declared, axioms defined parametrically.
/// Becomes an Instance when sorts are grounded and facts are added.
pub struct Theory {
    name: Option<String>,
    sorts: SlotMap<SortId, SortDecl>,
    symbols: SlotMap<SymbolId, SymbolDecl>,
    axioms: SlotMap<AxiomId, Axiom>,
}

impl Theory {
    pub fn sorts(&self) -> slotmap::basic::Iter<'_, SortId, SortDecl> {
        self.sorts.iter()
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
        info!("creating new empty theory");
        Self {
            name: None,
            sorts: SlotMap::with_key(),
            symbols: SlotMap::with_key(),
            axioms: SlotMap::with_key(),
        }
    }

    /// Construct a new empty theory with the given name.
    pub fn new_named(name: impl Into<String>) -> Self {
        let name = name.into();
        info!("creating new theory: {}", name);
        Self {
            name: Some(name),
            sorts: SlotMap::with_key(),
            symbols: SlotMap::with_key(),
            axioms: SlotMap::with_key(),
        }
    }

    /// Add a sort to the theory.
    pub fn declare_sort(&mut self, name: impl Into<String>) -> SortId {
        self.sorts.insert_with_key(|id| SortDecl {
            id,
            name: name.into(),
        })
    }

    /// Add a  predicate to the theory.
    pub fn declare_predicate(&mut self, name: impl Into<String>, params: Vec<SortId>) -> SymbolId {
        self.symbols.insert_with_key(|id| SymbolDecl {
            id,
            name: name.into(),
            signature: Some(Signature::new_predicate(params)),
        })
    }

    /// Add a function to the theory.
    pub fn declare_function(
        &mut self,
        name: impl Into<String>,
        params: Vec<SortId>,
        result: SortId,
    ) -> SymbolId {
        self.symbols.insert_with_key(|id| SymbolDecl {
            id,
            name: name.into(),
            signature: Some(Signature::new_function(params, result)),
        })
    }

    /// Declare a constant symbol (0-ary, no signature).
    pub fn declare_constant(&mut self, name: impl Into<String>) -> SymbolId {
        self.symbols.insert_with_key(|id| SymbolDecl {
            id,
            name: name.into(),
            signature: None,
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
        self.functions.entry(function).or_default().insert(args, value);
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

    /// Add a ground fact to the instance.
    pub fn add_fact(&mut self, fact: Atom) {
        self.facts.push(fact);
    }

    /// Deactivate an axiom (for ablation).
    pub fn deactivate_axiom(&mut self, id: AxiomId) {
        self.active_axioms.remove(&id);
    }

    /// Replace the active axiom set.
    pub fn set_active_axioms(&mut self, axioms: HashSet<AxiomId>) {
        self.active_axioms = axioms;
    }
}

pub trait ModelGenerator<'t> {
    fn generate(&mut self) -> GroundModel<'t>;
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
                manages(employee, employee),
                can_fire(employee, employee),
                reports_to(employee, employee),
            );

            functions!(
                works_in(employee) -> department,
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
