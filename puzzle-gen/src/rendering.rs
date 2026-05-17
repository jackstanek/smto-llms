//! Natural language rendering for theories and instances

use std::collections::HashMap;

use crate::theories::{ConstId, Formula, Instance};

pub mod template;

/// Interface for rendering instances and queries.
pub trait Renderer {
    /// Error type for rendering.
    type Error;

    /// Render an instance in natural language. If `fact_filter` is `Some`,
    /// only facts at those indices in `instance.facts()` are emitted —
    /// typically a load-bearing subset taken from a [`crate::solvers::Core`].
    async fn render(
        &self,
        query: &Formula,
        instance: &Instance<'_>,
        fact_filter: Option<&[usize]>,
    ) -> Result<String, Self::Error>;
}

/// Mapping from domain constants to their pretty (natural language) display
/// names. Distinct from the stable identifiers carried by `ConstDecl`, which
/// are reserved for SMT translation, debugging, and structured dumps.
pub type NameMap = HashMap<ConstId, String>;

/// Initializer for the name map: assigns a natural-language display name to
/// each domain constant in an `Instance`.
pub trait NameInitializer {
    fn init_map(&self, instance: &Instance<'_>, map: &mut NameMap);
}
