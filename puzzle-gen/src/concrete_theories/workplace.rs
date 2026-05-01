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

use rand::{Rng, seq::IndexedRandom};
use rand_distr::{Distribution, Poisson};

use crate::theories::{
    Atom, ConstId, Formula, GroundModel, ModelGenerator, QueryGenerator, SortId, SymbolId, Term,
    Theory,
};

/// Return a reference to the (lazily initialised) workplace `Theory`.
///
/// The `Theory` is built once and stored in a process-wide static.  Subsequent
/// calls return a reference to the same value with no allocation.
pub fn theory() -> &'static Theory {
    static THEORY: OnceLock<Theory> = OnceLock::new();
    THEORY.get_or_init(build)
}

/// Sampler for workplace puzzle queries.
///
/// Picks a uniformly-random ordered pair of distinct employees and a
/// uniformly-random *derived* authority predicate (`can_fire` or
/// `can_approve_expense`). Restricted to derived predicates because
/// non-derived ones (e.g. `manages`) are decided directly by the ground facts
/// regardless of which axioms remain active, so ablation would have no effect
/// on them and the puzzle would not exercise the implicit theory.
pub struct WorkplaceQueryGenerator<R> {
    rng: R,
}

impl<R> WorkplaceQueryGenerator<R> {
    pub fn new(rng: R) -> Self {
        Self { rng }
    }
}

impl<R> QueryGenerator<'static> for WorkplaceQueryGenerator<R>
where
    R: Rng,
{
    fn generate(&mut self, model: &GroundModel<'static>) -> Formula {
        let t = model.theory();
        let can_fire_sym = find_symbol(t, "can_fire");
        let can_approve_sym = find_symbol(t, "can_approve_expense");

        // Restrict to derived authority atoms so ablation exercises the oracle.
        let lfp = model.entailed_predicates();
        let derived: Vec<(SymbolId, ConstId, ConstId)> = lfp
            .iter()
            .filter_map(|(sym, args)| {
                if (*sym == can_fire_sym || *sym == can_approve_sym)
                    && args.len() == 2
                    && args[0] != args[1]
                {
                    Some((*sym, args[0], args[1]))
                } else {
                    None
                }
            })
            .collect();

        assert!(
            !derived.is_empty(),
            "no derived authority atoms — cannot generate a meaningful query"
        );

        let &(sym, p, q) = derived.choose(&mut self.rng).unwrap();
        Formula::Atom(Atom::Predicate {
            symbol: sym,
            args: vec![Term::DomainConst(p), Term::DomainConst(q)],
        })
    }
}

/// Construct the workplace `Theory`.  Called at most once by [`theory`].
fn build() -> Theory {
    theory! {
        // Natural language preamble
        preamble! (
            "The context for this logic puzzle is workplace relations.
            The domain is a company. You must construct a corporate name for the company.
            The company has a certain number of departments.
            Assign a name to each department, such as finance, human resources, engineering, and so on.
            There are also several employees, including the CEO, department heads, and other employees.
            Assign a name to each employee, making sure to have an even balance of male and female names.
            "
        );

        // ------------------------------------------------------------------
        // Sorts
        // ------------------------------------------------------------------
        sorts!(employee, department);

        // ------------------------------------------------------------------
        // Structural functions
        // Every employee works in at most one department.
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
            implicit: true,
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
            implicit: true,
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

/// Generator for ground truth workplace hierarchies.
pub struct WorkplaceGenerator<R> {
    rng: R,
    offspring_distr: Poisson<f64>,
    max_depth: usize,
    n_departments: usize,
}

impl<R> WorkplaceGenerator<R> {
    /// Create a new [`WorkplaceGenerator`], failing if the span of control is
    /// invalid for a [`Poisson`] distribution.
    pub fn try_new(
        rng: R,
        span_of_control: f64,
        max_depth: usize,
        n_departments: usize,
    ) -> Result<Self, rand_distr::PoissonError> {
        Poisson::new(span_of_control).map(|offspring_distr| Self {
            rng,
            offspring_distr,
            max_depth,
            n_departments,
        })
    }
}

fn find_sort(t: &Theory, name: &str) -> SortId {
    t.sorts()
        .find(|(_, s)| s.name() == name)
        .map(|(id, _)| id)
        .unwrap_or_else(|| panic!("workplace theory missing sort `{name}`"))
}

fn find_symbol(t: &Theory, name: &str) -> SymbolId {
    t.symbols()
        .find(|(_, s)| s.name() == name)
        .map(|(id, _)| id)
        .unwrap_or_else(|| panic!("workplace theory missing symbol `{name}`"))
}

impl<R> ModelGenerator<'static> for WorkplaceGenerator<R>
where
    R: Rng,
{
    fn generate(&mut self) -> GroundModel<'static> {
        let t = theory();
        let employee_sort = find_sort(t, "employee");
        let department_sort = find_sort(t, "department");
        let manages_sym = find_symbol(t, "manages");
        let works_in_sym = find_symbol(t, "works_in");

        let mut model = GroundModel::new(t);

        let departments: Vec<ConstId> = (0..self.n_departments)
            .map(|i| model.add_constant(format!("dept_{i}"), department_sort))
            .collect();

        let ceo = model.add_constant("ceo", employee_sort);

        // BFS frontier: (manager, depth, department).
        let mut frontier: VecDeque<(ConstId, usize, ConstId)> = VecDeque::new();
        for (i, &dept) in departments.iter().enumerate() {
            let head = model.add_constant(format!("head_{i}"), employee_sort);
            model.add_predicate_fact(manages_sym, vec![ceo, head]);
            model.add_function_fact(works_in_sym, vec![head], dept);
            frontier.push_back((head, 1, dept));
        }

        let mut next_id: usize = 0;
        while let Some((parent, depth, dept)) = frontier.pop_front() {
            if depth >= self.max_depth {
                continue;
            }
            let n_children = self.offspring_distr.sample(&mut self.rng) as usize;
            for _ in 0..n_children {
                let child = model.add_constant(format!("emp_{next_id}"), employee_sort);
                next_id += 1;
                model.add_predicate_fact(manages_sym, vec![parent, child]);
                model.add_function_fact(works_in_sym, vec![child], dept);
                frontier.push_back((child, depth + 1, dept));
            }
        }

        model
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
