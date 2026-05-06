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

use std::cell::RefCell;
use std::collections::{HashMap, VecDeque};
use std::sync::OnceLock;

use rand::{Rng, seq::IndexedRandom};
use rand_distr::{Distribution, Poisson};

use crate::rendering::{NameInitializer, NameMap};
use crate::theories::{
    Atom, ConstId, Formula, GroundModel, Instance, ModelGenerator, QueryGenerator, SortId,
    SymbolId, Term, Theory,
};

mod departments;
mod names;

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
        let can_fire_sym = t.find_symbol("can_fire");
        let can_approve_sym = t.find_symbol("can_approve_expense");

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

            <example_problem>

            Instance (2/10 axioms active)
              Domain:
                department (3): dept_0, dept_1, dept_2
                employee (24): ceo, head_0, head_1, head_2, emp_0, emp_1, emp_2, emp_3, emp_4, emp_5, emp_6, emp_7, emp_8, emp_9, emp_10, emp_11, emp_12, emp_13, emp_14, emp_15, emp_16, emp_17, emp_18, emp_19
              Active axioms:
                approved_implies_authority [explicit]
                  ∀ p: employee, q: employee. approved_expense(p, q) → can_approve_expense(p, q)
                fired_implies_authority [explicit]
                  ∀ p: employee, q: employee. fired(p, q) → can_fire(p, q)

            query: can_approve_expense(emp_3, emp_12)
            </example_probem>

            <example_puzzle>

            The Blue Harbor Corporation has three departments: Research,
            Marketing, and Operations. The employees include the CEO, department
            heads (Head Research, Head Marketing, Head Operations), and twenty
            other staff members: Alex, Brianna, Chris, Dana, Ethan, Fiona, Greg,
            Hannah, Ian, Julia, Kevin, Laura, Mark, Nancy, Olivia, Peter, Queen,
            Robert, Susan, and Thomas.

            Axioms:
            1. If an employee is approved to expense something for another employee, then the approving employee can approve the expense.
            2. If an employee is fired by another, then the firing employee can fire the first.

            Question: Can Dana approve an expense for Mark?

            </example_puzzle>
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
            works_in {
                (employee) -> department,
                nl: "{0} works in {ret}"
            },
        );

        // ------------------------------------------------------------------
        // Relations
        // ------------------------------------------------------------------
        predicates!(
            manages {
                (employee, employee),
                nl: "{0} manages {1}"
            },
            can_fire {
                (employee, employee),
                nl: "{0} can fire {1}"
            },
            can_approve_expense {
                (employee, employee),
                nl: "{0} can approve an expense for {1}"
            },
            fired {
                (employee, employee),
                nl: "{0} fired {1}"
            },
            approved_expense {
                (employee, employee),
                nl: "{0} approved an expense for {1}"
            },
        );

        // ------------------------------------------------------------------
        // A1. Direct managers can fire their reports.
        //     Typically stated explicitly in the puzzle.
        // ------------------------------------------------------------------
        horn! {
            name:     "direct_manager_can_fire",
            implicit: true,
            nl:       "Managers can fire their direct reports",
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
            nl:       "Anyone up the chain of command can fire someone below them",
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
            nl:       "Anyone up the chain of command can approve expenses for someone below them",
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

impl<R> ModelGenerator<'static> for WorkplaceGenerator<R>
where
    R: Rng,
{
    fn generate(&mut self) -> GroundModel<'static> {
        let t = theory();
        let employee_sort = t.find_sort("employee");
        let department_sort = t.find_sort("department");
        let manages_sym = t.find_symbol("manages");
        let works_in_sym = t.find_symbol("works_in");

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

/// Assigns pretty natural-language names to a workplace `Instance`'s domain
/// constants. Stable names like `dept_0`, `head_2`, `emp_7` are mapped to
/// real-sounding department names (Engineering, Finance, ...) and people
/// names (Alice, Brianna, ...). The CEO becomes `"the CEO"`; each department
/// head becomes `"the head of <pretty dept name>"`.
pub struct WorkplaceNameInitializer<R> {
    rng: RefCell<R>,
}

impl<R> WorkplaceNameInitializer<R> {
    pub fn new(rng: R) -> Self {
        Self {
            rng: RefCell::new(rng),
        }
    }
}

impl<R> NameInitializer for WorkplaceNameInitializer<R>
where
    R: Rng,
{
    fn init_map(&self, instance: &Instance<'_>, map: &mut NameMap) {
        let theory = instance.theory();
        let employee_sort = theory.find_sort("employee");
        let department_sort = theory.find_sort("department");

        let mut depts: Vec<(usize, ConstId)> = Vec::new();
        let mut heads: Vec<(usize, ConstId)> = Vec::new();
        let mut emps: Vec<(usize, ConstId)> = Vec::new();
        let mut ceo: Option<ConstId> = None;

        for (id, decl) in instance.constants() {
            let stable = decl.name();
            if decl.sort() == department_sort {
                if let Some(i) = stable.strip_prefix("dept_").and_then(|s| s.parse().ok()) {
                    depts.push((i, id));
                }
            } else if decl.sort() == employee_sort {
                if stable == "ceo" {
                    ceo = Some(id);
                } else if let Some(i) = stable.strip_prefix("head_").and_then(|s| s.parse().ok()) {
                    heads.push((i, id));
                } else if let Some(i) = stable.strip_prefix("emp_").and_then(|s| s.parse().ok()) {
                    emps.push((i, id));
                }
            }
        }

        depts.sort_by_key(|(i, _)| *i);
        heads.sort_by_key(|(i, _)| *i);
        emps.sort_by_key(|(i, _)| *i);

        let mut rng = self.rng.borrow_mut();

        let dept_names = departments::random_balanced_names(&mut *rng, depts.len());
        let mut dept_by_idx: HashMap<usize, String> = HashMap::new();
        for (&(idx, id), name) in depts.iter().zip(dept_names.iter()) {
            map.insert(id, name.to_string());
            dept_by_idx.insert(idx, name.to_string());
        }

        if let Some(id) = ceo {
            map.insert(id, "the CEO".to_string());
        }

        for &(idx, id) in &heads {
            let pretty = dept_by_idx
                .get(&idx)
                .cloned()
                .unwrap_or_else(|| format!("department {idx}"));
            map.insert(id, format!("the head of {pretty}"));
        }

        let emp_names = names::random_balanced_names(&mut *rng, emps.len());
        for (&(_, id), name) in emps.iter().zip(emp_names.iter()) {
            map.insert(id, name.to_string());
        }
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
        assert_eq!(implicit.len(), 8);

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
