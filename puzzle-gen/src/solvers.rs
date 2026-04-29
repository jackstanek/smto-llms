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
    /// ground facts and active axioms.
    fn load_instance(&mut self, instance: &Instance<'_>) -> Result<(), Self::Error>;

    /// Assert an additional axiom (e.g. one recovered from the oracle).
    fn assert_axiom(&mut self, axiom: &Axiom) -> Result<(), Self::Error>;

    /// Check whether a formula is entailed, refuted, or undetermined under the
    /// currently loaded instance.
    fn check_entailment(&mut self, query: &Formula) -> Result<QueryResult, Self::Error>;
}
