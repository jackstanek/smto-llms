//! Macros for ergonomic theory construction.
//!
//! # Term macros
//! - `var!(v)` — variable term
//! - `con!(c)` — constant term
//! - `app!(f, t1, t2, ...)` — function application term
//!
//! # Atom macros
//! - `pred!(p, t1, t2, ...)` — predicate application
//! - `eq!(t1, t2)` — equality
//! - `neq!(t1, t2)` — disequality
//!
//! # Axiom macros
//! All return the `AxiomId` assigned by the theory.
//!
//! ```ignore
//! horn!(theory,
//!     name: "direct_managers_fire",
//!     implicit: false,
//!     nl: "Direct managers can fire their reports",
//!     vars: [(p, emp_sort), (q, emp_sort)],
//!     body: [pred!(manages, var!(p), var!(q))],
//!     head: pred!(can_fire, var!(p), var!(q)),
//! );
//! ```

// ---------------------------------------------------------------------------
// Term constructors
// ---------------------------------------------------------------------------

/// Construct a variable term: `var!(v)` → `Term::Var(v)`.
#[macro_export]
macro_rules! var {
    ($v:expr) => {
        $crate::theories::Term::Var($v)
    };
}

/// Construct a constant term: `con!(c)` → `Term::Const(c)`.
#[macro_export]
macro_rules! con {
    ($c:expr) => {
        $crate::theories::Term::Const($c)
    };
}

/// Construct a function application term: `app!(f, t1, t2)` → `Term::App { .. }`.
#[macro_export]
macro_rules! app {
    ($f:expr $(,)?) => {
        $crate::theories::Term::App {
            symbol: $f,
            args: vec![],
        }
    };
    ($f:expr, $($arg:expr),+ $(,)?) => {
        $crate::theories::Term::App {
            symbol: $f,
            args: vec![$($arg),+],
        }
    };
}

// ---------------------------------------------------------------------------
// Atom constructors
// ---------------------------------------------------------------------------

/// Construct a predicate atom: `pred!(p, t1, t2)` → `Atom::Predicate { .. }`.
#[macro_export]
macro_rules! pred {
    ($p:expr $(,)?) => {
        $crate::theories::Atom::Predicate {
            symbol: $p,
            args: vec![],
        }
    };
    ($p:expr, $($arg:expr),+ $(,)?) => {
        $crate::theories::Atom::Predicate {
            symbol: $p,
            args: vec![$($arg),+],
        }
    };
}

/// Construct an equality atom: `eq!(t1, t2)` → `Atom::Eq(t1, t2)`.
#[macro_export]
macro_rules! eq {
    ($t1:expr, $t2:expr) => {
        $crate::theories::Atom::Eq($t1, $t2)
    };
}

/// Construct a disequality atom: `neq!(t1, t2)` → `Atom::Neq(t1, t2)`.
#[macro_export]
macro_rules! neq {
    ($t1:expr, $t2:expr) => {
        $crate::theories::Atom::Neq($t1, $t2)
    };
}

// ---------------------------------------------------------------------------
// Axiom macros
// ---------------------------------------------------------------------------

/// Add a Horn clause axiom to a theory: body₁ ∧ ... ∧ bodyₙ → head.
///
/// Returns the `AxiomId`.
///
/// ```ignore
/// horn!(theory,
///     name: "chain_fire",
///     category: AxiomCategory::Authority,
///     implicit: true,
///     nl: "Anyone up the chain of command can fire",
///     vars: [(p, emp), (q, emp)],
///     body: [pred!(manages_plus, var!(p), var!(q))],
///     head: pred!(can_fire, var!(p), var!(q)),
/// );
/// ```
#[macro_export]
macro_rules! horn {
    ($theory:expr,
     name: $name:literal,
     implicit: $imp:expr,
     nl: $nl:literal,
     vars: [$( ($v:expr, $s:expr) ),* $(,)?],
     body: [$( $body:expr ),* $(,)?],
     head: $head:expr
     $(, depends_on: [$( $dep:expr ),* $(,)?])?
     $(,)?
    ) => {
        $theory.add_axiom(
            $crate::theories::AxiomMeta::new(
                $name,
                $imp,
                $nl,
                vec![$($($dep),*)?],
            ),
            vec![$(($v, $s)),*],
            $crate::theories::AxiomBody::Horn {
                body: vec![$($body),*],
                head: $head,
            },
        )
    };
}

/// Add an integrity constraint axiom to a theory: ¬(body₁ ∧ ... ∧ bodyₙ).
///
/// Returns the `AxiomId`.
///
/// ```ignore
/// integrity!(theory,
///     name: "no_self_fire",
///     implicit: true,
///     nl: "No one can fire themselves",
///     vars: [(p, emp)],
///     body: [pred!(can_fire, var!(p), var!(p))],
/// );
/// ```
#[macro_export]
macro_rules! integrity {
    ($theory:expr,
     name: $name:literal,
     implicit: $imp:expr,
     nl: $nl:literal,
     vars: [$( ($v:expr, $s:expr) ),* $(,)?],
     body: [$( $body:expr ),+ $(,)?]
     $(, depends_on: [$( $dep:expr ),* $(,)?])?
     $(,)?
    ) => {
        $theory.add_axiom(
            $crate::theories::AxiomMeta::new(
                $name,
                $imp,
                $nl,
                vec![$($($dep),*)?],
            ),
            vec![$(($v, $s)),*],
            $crate::theories::AxiomBody::Integrity {
                body: vec![$($body),+],
            },
        )
    };
}

/// Add a functional fact axiom to a theory: f(args...) = value.
///
/// Returns the `AxiomId`.
///
/// ```ignore
/// functional!(theory,
///     name: "alice_works_at",
///     implicit: false,
///     nl: "Alice works at Acme",
///     symbol: works_at,
///     args: [con!(alice)],
///     value: con!(acme),
/// );
/// ```
#[macro_export]
macro_rules! functional {
    ($theory:expr,
     name: $name:literal,
     implicit: $imp:expr,
     nl: $nl:literal,
     symbol: $sym:expr,
     args: [$( $arg:expr ),* $(,)?],
     value: $val:expr
     $(, depends_on: [$( $dep:expr ),* $(,)?])?
     $(,)?
    ) => {
        $theory.add_axiom(
            $crate::theories::AxiomMeta::new(
                $name,
                $imp,
                $nl,
                vec![$($($dep),*)?],
            ),
            vec![],
            $crate::theories::AxiomBody::FunctionalFact {
                symbol: $sym,
                args: vec![$($arg),*],
                value: $val,
            },
        )
    };
}

/// Add a general formula axiom to a theory.
///
/// Returns the `AxiomId`.
///
/// ```ignore
/// general!(theory,
///     name: "custom_rule",
///     implicit: false,
///     nl: "A custom domain rule",
///     vars: [(p, emp)],
///     formula: Formula::Not(Box::new(Formula::Atom(pred!(can_fire, var!(p), var!(p))))),
/// );
/// ```
#[macro_export]
macro_rules! general {
    ($theory:expr,
     name: $name:literal,
     implicit: $imp:expr,
     nl: $nl:literal,
     vars: [$( ($v:expr, $s:expr) ),* $(,)?],
     formula: $formula:expr
     $(, depends_on: [$( $dep:expr ),* $(,)?])?
     $(,)?
    ) => {
        $theory.add_axiom(
            $crate::theories::AxiomMeta::new(
                $name,
                $imp,
                $nl,
                vec![$($($dep),*)?],
            ),
            vec![$(($v, $s)),*],
            $crate::theories::AxiomBody::General($formula),
        )
    };
}
