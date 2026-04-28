//! Concrete instantiation of the workplace hierarchy theory.
//!
//! The full reference encoding lives in `theories/workplace.smt`.  This module
//! expresses the predicate-logic subset that the current IR supports: Horn
//! clauses and integrity constraints over binary relations.  Function-valued
//! axioms (e.g. `works_in` coherence) require term-level support not yet in
//! the macro and are omitted here.
//!
//! # Axiom catalogue
//!
//! | ID | Name | `implicit_by_default` | Source |
//! |----|------|-----------------------|--------|
//! | A1 | `direct_manager_can_fire` | false | A1 in reference |
//! | A2 | `chain_of_command_can_fire` | true | A2 in reference |
//! | A3 | `direct_manager_can_approve` | false | A4 in reference |
//! | A4 | `chain_of_command_can_approve` | true | A4/A5 in reference |
//! | C1 | `fired_implies_authority` | false | C1 in reference |
//! | C2 | `approved_implies_authority` | false | C2 in reference |
//! | I1 | `no_self_fire` | true | I1 in reference |
//! | I2 | `no_self_approve` | true | I2 in reference |
//! | I3 | `no_self_manage` | true | S6/structural |
//! | I4 | `manages_antisymmetry` | true | S7 in reference |
//!
//! # Usage
//!
//! ```rust,ignore
//! let theory = workplace::theory();
//! let instance = theory.instantiate(domain);
//! ```

use std::{collections::VecDeque, sync::OnceLock};

use rand::Rng;
use rand_distr::{Distribution, Poisson};

use crate::theories::{GroundModel, ModelGenerator, Theory};

/// Return a reference to the (lazily initialised) workplace `Theory`.
///
/// The `Theory` is built once and stored in a process-wide static.  Subsequent
/// calls return a reference to the same value with no allocation.
pub fn theory() -> &'static Theory {
    static THEORY: OnceLock<Theory> = OnceLock::new();
    THEORY.get_or_init(build)
}

/// Construct the workplace `Theory`.  Called at most once by [`theory`].
fn build() -> Theory {
    theory! {
        // ------------------------------------------------------------------
        // Sorts
        // ------------------------------------------------------------------
        sorts!(employee, department);

        // ------------------------------------------------------------------
        // Structural functions
        // Every employee works in exactly one department.
        // (Axioms involving function terms are not yet expressed here; the
        //  function is declared for use by Instance-level SMT translation.)
        // ------------------------------------------------------------------
        functions!(
            works_in(employee) -> department,
        );

        // ------------------------------------------------------------------
        // Relations
        // ------------------------------------------------------------------
        predicates!(
            manages(employee, employee),
            can_fire(employee, employee),
            can_approve_expense(employee, employee),
            fired(employee, employee),
            approved_expense(employee, employee),
        );

        // ------------------------------------------------------------------
        // A1. Direct managers can fire their reports.
        //     Typically stated explicitly in the puzzle.
        // ------------------------------------------------------------------
        horn! {
            name:     "direct_manager_can_fire",
            implicit: false,
            nl:       "Direct managers can fire their reports",
            forall (p: employee, q: employee) {
                body: manages(p, q);
                head: can_fire(p, q);
            }
        };

        // ------------------------------------------------------------------
        // A2. Chain-of-command transitivity for can_fire.
        //     If p manages r and r can fire q, then p can fire q.
        //     Together with A1 this encodes the transitive closure of manages.
        //     This is the core implicit rule the LLM oracle must recover.
        // ------------------------------------------------------------------
        horn! {
            name:     "chain_of_command_can_fire",
            implicit: true,
            nl:       "Anyone up the chain of command can fire",
            forall (p: employee, r: employee, q: employee) {
                body: manages(p, r), can_fire(r, q);
                head: can_fire(p, q);
            }
        };

        // ------------------------------------------------------------------
        // A3. Direct managers can approve their reports' expenses.
        // ------------------------------------------------------------------
        horn! {
            name:     "direct_manager_can_approve",
            implicit: false,
            nl:       "Direct managers can approve their reports' expenses",
            forall (p: employee, q: employee) {
                body: manages(p, q);
                head: can_approve_expense(p, q);
            }
        };

        // ------------------------------------------------------------------
        // A4. Chain-of-command transitivity for can_approve_expense.
        // ------------------------------------------------------------------
        horn! {
            name:     "chain_of_command_can_approve",
            implicit: true,
            nl:       "Anyone up the chain of command can approve expenses",
            forall (p: employee, r: employee, q: employee) {
                body: manages(p, r), can_approve_expense(r, q);
                head: can_approve_expense(p, q);
            }
        };

        // ------------------------------------------------------------------
        // C1. Act coherence: firing implies authority.
        // ------------------------------------------------------------------
        horn! {
            name:     "fired_implies_authority",
            implicit: false,
            nl:       "If p fired q then p had authority to do so",
            forall (p: employee, q: employee) {
                body: fired(p, q);
                head: can_fire(p, q);
            }
        };

        // ------------------------------------------------------------------
        // C2. Act coherence: expense approval implies authority.
        // ------------------------------------------------------------------
        horn! {
            name:     "approved_implies_authority",
            implicit: false,
            nl:       "If p approved q's expense then p had authority to do so",
            forall (p: employee, q: employee) {
                body: approved_expense(p, q);
                head: can_approve_expense(p, q);
            }
        };

        // ------------------------------------------------------------------
        // I1. No one can fire themselves.
        // ------------------------------------------------------------------
        integrity! {
            name:     "no_self_fire",
            implicit: true,
            nl:       "No one can fire themselves",
            forall (p: employee) {
                body: can_fire(p, p);
            }
        };

        // ------------------------------------------------------------------
        // I2. No one can approve their own expenses.
        //     Classic integrity rule; a key trap for the oracle.
        // ------------------------------------------------------------------
        integrity! {
            name:     "no_self_approve",
            implicit: true,
            nl:       "No one can approve their own expenses",
            forall (p: employee) {
                body: can_approve_expense(p, p);
            }
        };

        // ------------------------------------------------------------------
        // I3. No one manages themselves.
        // ------------------------------------------------------------------
        integrity! {
            name:     "no_self_manage",
            implicit: true,
            nl:       "No one manages themselves",
            forall (p: employee) {
                body: manages(p, p);
            }
        };

        // ------------------------------------------------------------------
        // I4. The manages relation is anti-symmetric.
        //     If p manages q then q does not manage p.
        // ------------------------------------------------------------------
        integrity! {
            name:     "manages_antisymmetry",
            implicit: true,
            nl:       "The management relation is anti-symmetric",
            forall (p: employee, q: employee) {
                body: manages(p, q), manages(q, p);
            }
        };
    }
}

/// Generator for ground truth workplace
struct WorkplaceGenerator<R> {
    rng: R,
    offspring_distr: Poisson<f64>,
    max_depth: usize,
}

impl<R> WorkplaceGenerator<R> {
    /// Create a new [`WorkplaceGenerator`], failing if the span of control is
    /// invalid for a [`Poisson`] distribution.
    fn try_new(
        rng: R,
        span_of_control: f64,
        max_depth: usize,
    ) -> Result<Self, rand_distr::PoissonError> {
        Poisson::new(span_of_control).map(|offspring_distr| Self {
            rng,
            offspring_distr,
            max_depth,
        })
    }
}

impl<R> ModelGenerator for WorkplaceGenerator<R>
where
    R: Rng,
{
    fn generate(&mut self) -> GroundModel {
        let mut stack = VecDeque::new();
        // sample a root node
        stack.push_back((0, self.offspring_distr.sample(&mut self.rng)));
        while let Some(supervisor) = stack.pop_front() {}
        todo!()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn workplace_theory_structure() {
        let t = theory();

        // 2 sorts: employee, department
        assert_eq!(t.sorts().count(), 2);

        // 1 function + 5 predicates = 6 symbols
        assert_eq!(t.symbols().count(), 6);

        // 10 axioms total (6 horn + 4 integrity)
        assert_eq!(t.axioms().count(), 10);

        // 4 implicit axioms (A2, A4, I1-I4)
        let implicit: Vec<_> = t
            .axioms()
            .filter(|(_, a)| a.implicit_by_default())
            .collect();
        assert_eq!(implicit.len(), 6);

        // Spot-check names
        let names: std::collections::HashSet<&str> = t.axioms().map(|(_, a)| a.name()).collect();
        assert!(names.contains("chain_of_command_can_fire"));
        assert!(names.contains("no_self_approve"));
        assert!(names.contains("manages_antisymmetry"));
    }

    #[test]
    fn workplace_theory_is_singleton() {
        // Both calls must return the same address.
        let a = theory() as *const Theory;
        let b = theory() as *const Theory;
        assert_eq!(a, b);
    }
}
