//! Backends for solvers of various logics. Currently includes just SMT solvers,
//! but in the future could be datalog, ASP, other logics, etc.

use crate::theories::{AxiomId, Formula, Instance};

#[cfg(feature = "smt")]
pub mod smt;

#[cfg(feature = "smt")]
pub use smt::SmtBackend;

/// Subset of axioms + ground facts that the SMT solver reported as load-bearing
/// for a particular entailment verdict. `facts` are indices into the loaded
/// instance's `facts()` slice (see [`Instance::facts`]).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Core {
    pub axioms: Vec<AxiomId>,
    pub facts: Vec<usize>,
}

/// Result of an entailment check.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum QueryResult {
    /// T union F entails q.
    Entailed { core: Core },
    /// T union F entails not-q.
    Refuted { core: Core },
    /// Neither entailed nor refuted.
    Undetermined,
}

/// Backends which accept instantiated theories and answer entailment queries.
pub trait Backend {
    type Error;

    /// Load the instance: declare sorts, domain elements, symbols, then assert
    /// ground facts and axioms (gated on per-axiom activator literals).
    /// Must be called exactly once per backend.
    fn load_instance(&mut self, instance: &Instance<'_>) -> Result<(), Self::Error>;

    /// Sync the backend's active-axiom set with `instance.active_axioms()`.
    /// Cheap incremental ablation: flips activator literals in-memory and
    /// extends the CWA negation set as the LFP shrinks. Assumes the active
    /// set only ever shrinks across calls (monotone ablation).
    fn set_active_axioms(&mut self, instance: &Instance<'_>) -> Result<(), Self::Error>;

    /// Check whether a formula is entailed, refuted, or undetermined under the
    /// currently loaded instance and active axiom set.
    fn check_entailment(&mut self, query: &Formula) -> Result<QueryResult, Self::Error>;

    /// Like `check_entailment`, but assumes `expected` is the currently
    /// known status under a *superset* of the active axioms. Under monotone
    /// ablation the verdict can only stay at `expected` or degrade to
    /// `Undetermined` — never flip to the opposite verdict — so a single
    /// `check-sat` suffices. Panics if `expected` is `Undetermined`.
    fn recheck_entailment(
        &mut self,
        query: &Formula,
        expected: QueryResult,
    ) -> Result<QueryResult, Self::Error>;
}
