//! Macros for ergonomic theory construction.
//!
//! `theory!` matches `$($mac:ident ! $args:tt $(;)?)*`, where `$args:tt`
//! captures the entire argument group (`(...)` or `{...}`) as a single token
//! tree.  This is what keeps the expansion non-recursive: each statement is
//! handed to `theory_stmt!` as `mac ! args` in one flat pass.
//!
//! # Usage
//!
//! ```rust,ignore
//! let t = theory! {
//!     sorts!(Employee, Department);
//!
//!     predicates!(
//!         manages(Employee, Employee),
//!         can_fire(Employee, Employee),
//!     );
//!
//!     functions!(
//!         works_in(Employee) -> Department,
//!     );
//!
//!     constants!(alice, bob, engineering);
//!
//!     horn! {
//!         name: "manages_can_fire",
//!         implicit: false,
//!         nl: "Managers can fire their direct reports",
//!         forall (x: Employee, y: Employee) {
//!             body: manages(x, y);
//!             head: can_fire(x, y);
//!         }
//!     };
//!
//!     integrity! {
//!         name: "no_self_manage",
//!         implicit: true,
//!         nl: "Nobody manages themselves",
//!         forall (x: Employee) {
//!             body: manages(x, x);
//!         }
//!     };
//! };
//! ```
//!
//! ## Scope and ordering
//!
//! All `let` bindings from `sorts!`, `predicates!`, `functions!`, and
//! `constants!` are emitted sequentially, so later statements can reference
//! `SortId`/`SymbolId` variables declared earlier.  Variables declared inside
//! `forall (...)` are local to their axiom block and do not escape.
//!
//! ## Constants vs. domain elements
//!
//! `constants!` declares named 0-ary symbols at the **Theory** level.
//! Finite domain elements for `Instance` are supplied via `Theory::instantiate`.

// ---------------------------------------------------------------------------
// theory_stmt! — single-statement, non-recursive handler
//
// Called by theory! as `theory_stmt!(__theory, mac ! args)`.
// Each arm matches one `mac ! args` pair with no recursion.
// ---------------------------------------------------------------------------

macro_rules! theory_stmt {
    // ------------------------------------------------------------------
    // sorts!(S, T, ...)
    // ------------------------------------------------------------------
    ($t:ident, sorts ! ($($sort:ident),* $(,)?)) => {
        $(
            #[allow(unused_variables)]
            let $sort = $t.declare_sort(stringify!($sort));
        )*
    };

    // ------------------------------------------------------------------
    // predicates!(p(S1, S2), q(S), ...)
    // ------------------------------------------------------------------
    ($t:ident, predicates ! ($($pred:ident ( $($param:ident),* $(,)? )),* $(,)?)) => {
        $(
            let $pred = $t.declare_predicate(stringify!($pred), vec![$($param),*]);
        )*
    };

    // ------------------------------------------------------------------
    // functions!(f(S1, S2) -> R, ...)
    // ------------------------------------------------------------------
    ($t:ident, functions ! ($($func:ident ( $($param:ident),* $(,)? ) -> $ret:ident),* $(,)?)) => {
        $(
            #[allow(unused_variables)]
            let $func = $t.declare_function(stringify!($func), vec![$($param),*], $ret);
        )*
    };

    // ------------------------------------------------------------------
    // constants!(a, b, c)
    // ------------------------------------------------------------------
    ($t:ident, constants ! ($($con:ident),* $(,)?)) => {
        $(
            #[allow(unused_variables)]
            let $con = $t.declare_constant(stringify!($con));
        )*
    };

    // ------------------------------------------------------------------
    // horn! { name: ..., implicit: ..., nl: ...,
    //         forall (...) { body: ...; head: ...; } }
    // ------------------------------------------------------------------
    ($t:ident, horn ! {
        name:     $name:expr,
        implicit: $implicit:expr,
        nl:       $nl:expr,
        forall ($($var:ident : $sort_var:ident),* $(,)?) {
            body: $($bpred:ident ( $($barg:ident),* )),+ $(,)? ;
            head: $hpred:ident ( $($harg:ident),* ) $(,)? ;
        }
    }) => {
        {
            let mut __var_idx: u32 = 0;
            $(
                #[allow(unused_variables)]
                let $var = {
                    let __v = $crate::theories::VarId(__var_idx);
                    __var_idx += 1;
                    __v
                };
            )*
            let __vars: Vec<($crate::theories::VarId, $crate::theories::SortId)> =
                vec![$(($var, $sort_var)),*];
            let __body: Vec<$crate::theories::Atom> = vec![
                $(
                    $crate::theories::Atom::Predicate {
                        symbol: $bpred,
                        args: vec![$( $crate::theories::Term::Var($barg) ),*],
                    }
                ),+
            ];
            let __head = $crate::theories::Atom::Predicate {
                symbol: $hpred,
                args: vec![$( $crate::theories::Term::Var($harg) ),*],
            };
            let __meta = $crate::theories::AxiomMeta::new($name, $implicit, $nl, vec![]);
            $t.add_axiom(
                __meta,
                __vars,
                $crate::theories::AxiomBody::Horn { body: __body, head: __head },
            );
        }
    };

    // ------------------------------------------------------------------
    // integrity! { name: ..., implicit: ..., nl: ...,
    //              forall (...) { body: ...; } }
    // ------------------------------------------------------------------
    ($t:ident, integrity ! {
        name:     $name:expr,
        implicit: $implicit:expr,
        nl:       $nl:expr,
        forall ($($var:ident : $sort_var:ident),* $(,)?) {
            body: $($bpred:ident ( $($barg:ident),* )),+ $(,)? ;
        }
    }) => {
        {
            let mut __var_idx: u32 = 0;
            $(
                #[allow(unused_variables)]
                let $var = {
                    let __v = $crate::theories::VarId(__var_idx);
                    __var_idx += 1;
                    __v
                };
            )*
            let __vars: Vec<($crate::theories::VarId, $crate::theories::SortId)> =
                vec![$(($var, $sort_var)),*];
            let __body: Vec<$crate::theories::Atom> = vec![
                $(
                    $crate::theories::Atom::Predicate {
                        symbol: $bpred,
                        args: vec![$( $crate::theories::Term::Var($barg) ),*],
                    }
                ),+
            ];
            let __meta = $crate::theories::AxiomMeta::new($name, $implicit, $nl, vec![]);
            $t.add_axiom(
                __meta,
                __vars,
                $crate::theories::AxiomBody::Integrity { body: __body },
            );
        }
    };
}

// ---------------------------------------------------------------------------
// theory! — single-pass, non-recursive dispatcher
//
// Each statement is `mac ! args` where `args` is a single token tree
// (`(...)` for sorts/predicates/functions/constants, `{...}` for axioms).
// The `$args:tt` fragment keeps the expansion flat: no $($rest:tt)* passing,
// no recursion regardless of theory size.
// ---------------------------------------------------------------------------

/// Build a [`Theory`][crate::theories::Theory] from a concise DSL.
///
/// Accepts a sequence of `mac!(...)` or `mac!{...}` statements separated by
/// optional semicolons.  Supported forms:
///
/// | Form | Effect |
/// |------|--------|
/// | `sorts!(S, T, ...)` | Declare sorts; bind `SortId`s to the identifiers |
/// | `predicates!(p(S1, S2), ...)` | Declare predicate symbols |
/// | `functions!(f(S1) -> R, ...)` | Declare function symbols |
/// | `constants!(a, b, ...)` | Declare 0-ary named constants |
/// | `horn! { name: ..., implicit: ..., nl: ..., forall (...) { body: ...; head: ...; } }` | Horn axiom |
/// | `integrity! { name: ..., implicit: ..., nl: ..., forall (...) { body: ...; } }` | Integrity constraint |
macro_rules! theory {
    (
        $($mac:ident ! $args:tt $(;)?)*
    ) => {{
        let mut __theory = $crate::theories::Theory::new();
        $(
            theory_stmt!(__theory, $mac ! $args);
        )*
        __theory
    }};
}
