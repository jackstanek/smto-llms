//! Representation of a first-order theory with implicit axioms.

use std::collections::{HashMap, HashSet};

use slotmap::{SlotMap, new_key_type};

new_key_type! {
    /// Identifiers for sorts
    pub struct SortId;

    /// Identifiers for function symbols
    pub struct SymbolId;

    /// Identifiers for axioms
    pub struct AxiomId;

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
    /// Constant denoted by a symbol
    Const(SymbolId),
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

    pub fn meta(&self) -> &AxiomMeta {
        &self.meta
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
    name: String,
    sorts: SlotMap<SortId, SortDecl>,
    symbols: SlotMap<SymbolId, SymbolDecl>,
    axioms: SlotMap<AxiomId, Axiom>,
}

/// An instantiated theory: all sorts have concrete domains, plus ground facts
/// and (optionally) a query.
pub struct Instance<'t> {
    theory: &'t Theory,
    domain: HashMap<SortId, Vec<SymbolId>>, // Sort -> enumerated constants
    facts: Vec<Atom>,                       // all ground
    active_axioms: HashSet<AxiomId>,        // for ablation
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

    pub fn axiom(&self, id: AxiomId) -> &Axiom {
        &self.axioms[id]
    }

    /// Construct a new empty theory with the given name.
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
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

    /// Add a predicate to the theory.
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

    /// Instantiate the theory with the given finite domain.
    pub fn instantiate(&self, domain: HashMap<SortId, Vec<SymbolId>>) -> Instance<'_> {
        let active_axioms = self.axioms.iter().map(|(id, _)| id).collect::<HashSet<_>>();
        Instance {
            theory: self,
            domain,
            facts: Vec::new(),
            active_axioms,
        }
    }
}

impl<'t> Instance<'t> {
    pub fn theory(&self) -> &'t Theory {
        self.theory
    }

    pub fn domain(&self) -> &HashMap<SortId, Vec<SymbolId>> {
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

#[cfg(test)]
mod tests {
    use super::*;

    /// Smoke-test: build a small workplace theory using the macros and check
    /// that all axiom variants round-trip through the Theory.
    #[test]
    fn macro_theory_construction() {
        let mut t = Theory::new("workplace");

        // Sorts
        let emp = t.declare_sort("Employee");
        let dept = t.declare_sort("Department");

        // Symbols
        let manages = t.declare_predicate("manages", vec![emp, emp]);
        let can_fire = t.declare_predicate("can_fire", vec![emp, emp]);
        let works_in = t.declare_function("works_in", vec![emp], dept);
        let alice = t.declare_constant("alice");
        let bob = t.declare_constant("bob");
        let engineering = t.declare_constant("engineering");

        // Variables
        let p = VarId(0);
        let q = VarId(1);

        // Horn: manages(p,q) => can_fire(p,q)
        let a1 = horn!(t,
            name: "direct_managers_fire",
            implicit: false,
            nl: "Direct managers can fire their reports",
            vars: [(p, emp), (q, emp)],
            body: [pred!(manages, var!(p), var!(q))],
            head: pred!(can_fire, var!(p), var!(q)),
        );

        // Integrity: not(can_fire(p,p))
        let a2 = integrity!(t,
            name: "no_self_fire",
            implicit: true,
            nl: "No one can fire themselves",
            vars: [(p, emp)],
            body: [pred!(can_fire, var!(p), var!(p))],
        );

        // Functional: works_in(alice) = engineering
        let a3 = functional!(t,
            name: "alice_works_in_eng",
            implicit: false,
            nl: "Alice works in engineering",
            symbol: works_in,
            args: [con!(alice)],
            value: con!(engineering),
        );

        // General: forall p q. manages(p,q) => can_fire(p,q)  (redundant, just testing the macro)
        let a4 = general!(t,
            name: "custom_rule",
            implicit: false,
            nl: "A custom domain rule",
            vars: [(p, emp), (q, emp)],
            formula: Formula::Implies(
                Box::new(Formula::Atom(pred!(manages, var!(p), var!(q)))),
                Box::new(Formula::Atom(pred!(can_fire, var!(p), var!(q)))),
            ),
        );

        // Horn with depends_on
        let _a5 = horn!(t,
            name: "derived_fire",
            implicit: true,
            nl: "Derived from direct managers fire",
            vars: [(p, emp), (q, emp)],
            body: [pred!(manages, var!(p), var!(q))],
            head: pred!(can_fire, var!(p), var!(q)),
            depends_on: [a1],
        );

        // Verify axiom metadata
        assert_eq!(t.axiom(a1).meta().name(), "direct_managers_fire");
        assert!(!t.axiom(a1).meta().implicit_by_default());
        assert_eq!(t.axiom(a2).meta().name(), "no_self_fire");
        assert!(t.axiom(a2).meta().implicit_by_default());
        assert_eq!(t.axiom(a3).meta().name(), "alice_works_in_eng");
        assert_eq!(t.axiom(a4).meta().name(), "custom_rule");

        // Verify vars
        assert_eq!(t.axiom(a1).vars().len(), 2);
        assert_eq!(t.axiom(a2).vars().len(), 1);
        assert_eq!(t.axiom(a3).vars().len(), 0); // functional facts are ground

        // Verify body variant
        assert!(matches!(t.axiom(a1).body(), AxiomBody::Horn { .. }));
        assert!(matches!(t.axiom(a2).body(), AxiomBody::Integrity { .. }));
        assert!(matches!(
            t.axiom(a3).body(),
            AxiomBody::FunctionalFact { .. }
        ));
        assert!(matches!(t.axiom(a4).body(), AxiomBody::General(_)));

        // Verify term/atom macros produce expected structure
        let term_v = var!(p);
        assert!(matches!(term_v, Term::Var(VarId(0))));

        let term_c = con!(alice);
        assert!(matches!(term_c, Term::Const(_)));

        let term_app = app!(works_in, var!(p));
        assert!(matches!(term_app, Term::App { .. }));

        let atom_p = pred!(manages, var!(p), var!(q));
        assert!(matches!(atom_p, Atom::Predicate { .. }));

        let atom_eq = eq!(var!(p), var!(q));
        assert!(matches!(atom_eq, Atom::Eq(..)));

        let atom_neq = neq!(var!(p), var!(q));
        assert!(matches!(atom_neq, Atom::Neq(..)));

        // Verify instantiation with all axioms active
        let domain = HashMap::from([(emp, vec![alice, bob]), (dept, vec![engineering])]);
        let instance = t.instantiate(domain);
        assert_eq!(instance.active_axioms().len(), 5);
    }
}
