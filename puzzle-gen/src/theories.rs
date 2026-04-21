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
    category: AxiomCategory,
    implicit_by_default: bool,
    natural_language: String,
    depends_on: Vec<AxiomId>,
}

impl AxiomMeta {
    pub fn new(
        name: impl Into<String>,
        category: AxiomCategory,
        implicit_by_default: bool,
        natural_language: impl Into<String>,
        depends_on: Vec<AxiomId>,
    ) -> Self {
        Self {
            name: name.into(),
            category,
            implicit_by_default,
            natural_language: natural_language.into(),
            depends_on,
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn category(&self) -> AxiomCategory {
        self.category
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

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum AxiomCategory {
    Structural,   // sort/symbol coherence, functionality
    Derived,      // chain_of_command, same_company, etc.
    Authority,    // can_fire, can_approve_expense
    ActCoherence, // fired -> can_fire
    Integrity,    // no_self_fire, no_self_approve
    Domain,       // catch-all for domain-specific rules
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
