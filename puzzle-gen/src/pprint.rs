//! Pretty-printing for [`Instance`], [`Axiom`], [`Formula`], and related IR
//! types.
//!
//! # Entry points
//!
//! - [`PrettyAxiom`] — wraps a single axiom plus its theory; implements
//!   [`Display`].  Prints the axiom name, explicit/implicit tag, and a
//!   quantified formula using the theory's declared names.
//! - [`PrettyFormula`] — wraps a [`Formula`] plus an [`Instance`] (for
//!   constant name resolution); implements [`Display`].  Handles all formula
//!   variants recursively.
//! - [`PrettyInstance`] — wraps an instance; implements [`Display`].  Prints
//!   the domain and **only** the currently active axioms.
//!
//! # Example output
//!
//! ```text
//! Instance (6 / 10 axioms active)
//!   Domain:
//!     department (3): dept_0, dept_1, dept_2
//!     employee (7): ceo, head_0, head_1, head_2, emp_0, emp_1, emp_2
//!   Active axioms:
//!     chain_of_command_can_approve [implicit]
//!       ∀ p: employee, r: employee, q: employee.
//!         manages(p, r) ∧ can_approve_expense(r, q) → can_approve_expense(p, q)
//!     direct_manager_can_fire [explicit]
//!       ∀ p: employee, q: employee. manages(p, q) → can_fire(p, q)
//! ```

use std::{
    collections::HashMap,
    fmt::{self, Write as _},
};

use crate::theories::{Atom, AxiomBody, ConstId, Formula, Instance, SortId, Term, Theory, VarId};

// -- Variable naming ---------------------------------------------------------

const VAR_NAMES: &[&str] = &["p", "q", "r", "s", "t", "u", "v", "w"];

fn var_name(idx: usize) -> String {
    VAR_NAMES
        .get(idx)
        .map_or_else(|| format!("v{idx}"), |s| s.to_string())
}

fn make_var_map(vars: &[(VarId, SortId)]) -> HashMap<VarId, String> {
    vars.iter()
        .enumerate()
        .map(|(i, &(v, _))| (v, var_name(i)))
        .collect()
}

// -- Low-level term/atom formatters ------------------------------------------

struct FmtTerm<'a> {
    term: &'a Term,
    theory: &'a Theory,
    var_map: &'a HashMap<VarId, String>,
    const_names: &'a HashMap<ConstId, &'a str>,
}

impl<'a> FmtTerm<'a> {
    fn child(&self, term: &'a Term) -> Self {
        FmtTerm { term, ..*self }
    }
}

impl fmt::Display for FmtTerm<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.term {
            Term::Var(v) => match self.var_map.get(v) {
                Some(n) => f.write_str(n),
                None => write!(f, "?v{}", v.0),
            },
            Term::DomainConst(c) => match self.const_names.get(c) {
                Some(n) => f.write_str(n),
                None => f.write_str("?const"),
            },
            Term::Const(s) => f.write_str(self.theory.symbol(*s).name()),
            Term::App { symbol, args } => {
                write!(f, "{}(", self.theory.symbol(*symbol).name())?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        f.write_str(", ")?;
                    }
                    self.child(arg).fmt(f)?;
                }
                f.write_char(')')
            }
        }
    }
}

struct FmtAtom<'a> {
    atom: &'a Atom,
    theory: &'a Theory,
    var_map: &'a HashMap<VarId, String>,
    const_names: &'a HashMap<ConstId, &'a str>,
}

impl<'a> FmtAtom<'a> {
    fn term(&self, t: &'a Term) -> FmtTerm<'a> {
        FmtTerm {
            term: t,
            theory: self.theory,
            var_map: self.var_map,
            const_names: self.const_names,
        }
    }
}

impl fmt::Display for FmtAtom<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.atom {
            Atom::Predicate { symbol, args } => {
                write!(f, "{}(", self.theory.symbol(*symbol).name())?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        f.write_str(", ")?;
                    }
                    self.term(arg).fmt(f)?;
                }
                f.write_char(')')
            }
            Atom::Eq(t1, t2) => write!(f, "{} = {}", self.term(t1), self.term(t2)),
            Atom::Neq(t1, t2) => write!(f, "{} ≠ {}", self.term(t1), self.term(t2)),
        }
    }
}

// -- Public API --------------------------------------------------------------

/// Display wrapper for a single [`Axiom`][crate::theories::Axiom].
///
/// Prints the axiom name, explicit/implicit tag, and a quantified formula that
/// uses the theory's declared sort and symbol names.
pub struct PrettyAxiom<'a> {
    pub axiom: &'a crate::theories::Axiom,
    pub theory: &'a Theory,
}

impl fmt::Display for PrettyAxiom<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let axiom = self.axiom;
        let theory = self.theory;
        let tag = if axiom.implicit_by_default() {
            "implicit"
        } else {
            "explicit"
        };
        writeln!(f, "{} [{tag}]", axiom.name())?;

        let var_map = make_var_map(axiom.vars());
        let no_consts: HashMap<ConstId, &str> = HashMap::new();

        macro_rules! atom {
            ($a:expr) => {
                FmtAtom {
                    atom: $a,
                    theory,
                    var_map: &var_map,
                    const_names: &no_consts,
                }
            };
        }

        // Quantifier prefix
        if axiom.vars().is_empty() {
            f.write_str("  ")?;
        } else {
            f.write_str("  ∀")?;
            for (i, &(var, sort)) in axiom.vars().iter().enumerate() {
                if i > 0 {
                    f.write_char(',')?;
                }
                write!(f, " {}: {}", var_map[&var], theory.sort(sort).name())?;
            }
            f.write_str(". ")?;
        }

        // Body
        match axiom.body() {
            AxiomBody::Horn { body, head } => {
                // Wrap long bodies onto a new indented line when there are multiple atoms.
                if body.len() > 1 {
                    f.write_char('\n')?;
                    f.write_str("    ")?;
                }
                for (i, a) in body.iter().enumerate() {
                    if i > 0 {
                        f.write_str(" ∧ ")?;
                    }
                    write!(f, "{}", atom!(a))?;
                }
                if body.len() > 1 {
                    f.write_str("\n    ")?;
                }
                write!(f, " → {}", atom!(head))?;
            }
            AxiomBody::Integrity { body } => {
                f.write_str("¬(")?;
                for (i, a) in body.iter().enumerate() {
                    if i > 0 {
                        f.write_str(" ∧ ")?;
                    }
                    write!(f, "{}", atom!(a))?;
                }
                f.write_char(')')?;
            }
            AxiomBody::FunctionalFact {
                symbol,
                args,
                value,
            } => {
                let no_vars: HashMap<VarId, String> = HashMap::new();
                write!(f, "{}(", theory.symbol(*symbol).name())?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        f.write_str(", ")?;
                    }
                    FmtTerm {
                        term: arg,
                        theory,
                        var_map: &no_vars,
                        const_names: &no_consts,
                    }
                    .fmt(f)?;
                }
                write!(
                    f,
                    ") = {}",
                    FmtTerm {
                        term: value,
                        theory,
                        var_map: &no_vars,
                        const_names: &no_consts
                    }
                )?;
            }
            AxiomBody::General(_) => {
                f.write_str("<general formula>")?;
            }
        }

        Ok(())
    }
}

// -- Formula pretty-printer --------------------------------------------------

/// Operator precedence levels, lowest to highest, for parenthesisation.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Prec {
    Implies, // lowest
    Or,
    And,
    Not,
    Atom, // highest – never needs parens
}

fn formula_prec(f: &Formula) -> Prec {
    match f {
        Formula::Implies(..) => Prec::Implies,
        Formula::Or(..) => Prec::Or,
        Formula::And(..) => Prec::And,
        Formula::Not(..) => Prec::Not,
        Formula::Atom(..) | Formula::Forall(..) | Formula::Exists(..) => Prec::Atom,
    }
}

/// Recursive formula writer.
///
/// `var_map` is cloned and extended when entering quantifiers so that the
/// caller's map is unchanged after each recursive call.
fn write_formula(
    out: &mut fmt::Formatter<'_>,
    formula: &Formula,
    theory: &Theory,
    var_map: &mut HashMap<VarId, String>,
    const_names: &HashMap<ConstId, &str>,
    next_var: &mut usize,
    // Minimum precedence of the context; sub-expressions with lower prec get parens.
    ctx_prec: Prec,
) -> fmt::Result {
    let needs_parens = formula_prec(formula) < ctx_prec;
    if needs_parens {
        out.write_char('(')?;
    }

    match formula {
        Formula::Atom(atom) => {
            write!(
                out,
                "{}",
                FmtAtom {
                    atom,
                    theory,
                    var_map,
                    const_names
                }
            )?;
        }
        Formula::Not(inner) => {
            out.write_str("¬")?;
            write_formula(
                out,
                inner,
                theory,
                var_map,
                const_names,
                next_var,
                Prec::Not,
            )?;
        }
        Formula::And(children) => {
            for (i, child) in children.iter().enumerate() {
                if i > 0 {
                    out.write_str(" ∧ ")?;
                }
                write_formula(
                    out,
                    child,
                    theory,
                    var_map,
                    const_names,
                    next_var,
                    Prec::And,
                )?;
            }
        }
        Formula::Or(children) => {
            for (i, child) in children.iter().enumerate() {
                if i > 0 {
                    out.write_str(" ∨ ")?;
                }
                write_formula(out, child, theory, var_map, const_names, next_var, Prec::Or)?;
            }
        }
        Formula::Implies(ante, cons) => {
            write_formula(out, ante, theory, var_map, const_names, next_var, Prec::Or)?;
            out.write_str(" → ")?;
            write_formula(
                out,
                cons,
                theory,
                var_map,
                const_names,
                next_var,
                Prec::Implies,
            )?;
        }
        Formula::Forall(vars, body) | Formula::Exists(vars, body) => {
            let q = if matches!(formula, Formula::Forall(..)) {
                "∀"
            } else {
                "∃"
            };
            out.write_str(q)?;
            let mut extended = var_map.clone();
            for &(var, sort) in vars {
                let name = var_name(*next_var);
                *next_var += 1;
                extended.insert(var, name.clone());
                write!(out, " {}: {}", name, theory.sort(sort).name())?;
            }
            out.write_str(". ")?;
            write_formula(
                out,
                body,
                theory,
                &mut extended,
                const_names,
                next_var,
                Prec::Implies,
            )?;
        }
    }

    if needs_parens {
        out.write_char(')')?;
    }
    Ok(())
}

/// Display wrapper for a [`Formula`].
///
/// Requires an [`Instance`] to resolve domain constant names.  Variable names
/// in quantifiers are assigned fresh names from the `p, q, r, ...` sequence.
pub struct PrettyFormula<'a, 't> {
    pub formula: &'a Formula,
    pub instance: &'a Instance<'t>,
}

impl<'a, 't> PrettyFormula<'a, 't> {
    pub fn from(formula: &'a Formula, instance: &'a Instance<'t>) -> Self {
        Self { formula, instance }
    }
}

impl fmt::Display for PrettyFormula<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let theory = self.instance.theory();
        let const_names: HashMap<ConstId, &str> = self
            .instance
            .constants()
            .iter()
            .map(|(id, decl)| (id, decl.name()))
            .collect();
        let mut var_map = HashMap::new();
        let mut next_var = 0usize;
        write_formula(
            f,
            self.formula,
            theory,
            &mut var_map,
            &const_names,
            &mut next_var,
            Prec::Implies,
        )
    }
}

// ---------------------------------------------------------------------------

/// Display wrapper for an [`Instance`].
///
/// Shows the domain constants grouped by sort and all currently **active**
/// axioms in alphabetical order.
pub struct PrettyInstance<'a, 't> {
    pub instance: &'a Instance<'t>,
}

impl<'a, 't> From<&'a Instance<'t>> for PrettyInstance<'a, 't> {
    fn from(instance: &'a Instance<'t>) -> Self {
        Self { instance }
    }
}

impl<'a, 't> fmt::Display for PrettyInstance<'a, 't> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let inst = self.instance;
        let theory = inst.theory();
        let n_active = inst.active_axioms().len();
        let n_total = theory.axioms().count();

        writeln!(f, "Instance ({n_active}/{n_total} axioms active)")?;

        // Domain, sorted by sort name for stable output.
        writeln!(f, "  Domain:")?;
        let mut sorts: Vec<_> = theory.sorts().collect();
        sorts.sort_by_key(|(_, s)| s.name());
        for (sort_id, sort_decl) in &sorts {
            let consts = inst
                .domain()
                .get(sort_id)
                .map_or(&[] as &[ConstId], Vec::as_slice);
            let names: Vec<&str> = consts.iter().map(|c| inst.constant(*c).name()).collect();
            writeln!(
                f,
                "    {} ({}): {}",
                sort_decl.name(),
                consts.len(),
                names.join(", ")
            )?;
        }

        // Active axioms, sorted by name for stable output.
        writeln!(f, "  Active axioms:")?;
        let mut active: Vec<_> = inst
            .active_axioms()
            .iter()
            .map(|&id| theory.axiom(id))
            .collect();
        active.sort_by_key(|a| a.name());

        for axiom in active {
            let pretty = PrettyAxiom { axiom, theory };
            // Print each line of the axiom indented by 4 spaces.
            for line in pretty.to_string().lines() {
                writeln!(f, "    {line}")?;
            }
        }

        Ok(())
    }
}
