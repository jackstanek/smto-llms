//! Backends for solvers of various logics. Currently includes just SMT solvers,
//! but in the future could be datalog, ASP, other logics, etc.

use crate::theories::{Axiom, Formula, Instance};

pub mod smt;

pub use smt::SmtBackend;

/// Result of an entailment check.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QueryResult {
    /// T union F entails q.
    Entailed,
    /// T union F entails not-q.
    Refuted,
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
