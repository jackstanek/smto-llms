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

// ---------------------------------------------------------------------------
// predicate_decl! / function_decl! — per-entry dispatch for the
// with-NL-template vs. without-NL-template forms used by predicates! and
// functions!. Returning a `SymbolId` so the call site can `let`-bind it.
// ---------------------------------------------------------------------------

/// Builds a single atom for a Horn (or integrity) rule body. Two shapes:
///   `pred(args)`            -> Atom::Predicate
///   `func(args) = ident`    -> Atom::Eq(Term::App, Term::Var)  (function-equality)
macro_rules! horn_body_atom {
    ($sym:ident ( $($a:ident),* $(,)? ) = $rhs:ident) => {
        $crate::theories::Atom::Eq(
            $crate::theories::Term::App {
                symbol: $sym,
                args: vec![ $( $crate::theories::Term::Var($a) ),* ],
            },
            $crate::theories::Term::Var($rhs),
        )
    };
    ($sym:ident ( $($a:ident),* $(,)? )) => {
        $crate::theories::Atom::Predicate {
            symbol: $sym,
            args: vec![ $( $crate::theories::Term::Var($a) ),* ],
        }
    };
}

macro_rules! predicate_decl {
    ($t:ident, $pred:ident, { ( $($param:ident),* $(,)? ), nl: $nl:expr, cwa: $cwa:expr $(,)? }) => {
        $t.declare_predicate(stringify!($pred), vec![$($param),*], Some($nl), $cwa)
    };
    ($t:ident, $pred:ident, { ( $($param:ident),* $(,)? ), cwa: $cwa:expr, nl: $nl:expr $(,)? }) => {
        $t.declare_predicate(stringify!($pred), vec![$($param),*], Some($nl), $cwa)
    };
    ($t:ident, $pred:ident, { ( $($param:ident),* $(,)? ), cwa: $cwa:expr $(,)? }) => {
        $t.declare_predicate(stringify!($pred), vec![$($param),*], None::<String>, $cwa)
    };
    ($t:ident, $pred:ident, { ( $($param:ident),* $(,)? ), nl: $nl:expr $(,)? }) => {
        $t.declare_predicate(stringify!($pred), vec![$($param),*], Some($nl), false)
    };
    ($t:ident, $pred:ident, { ( $($param:ident),* $(,)? ) $(,)? }) => {
        $t.declare_predicate(stringify!($pred), vec![$($param),*], None::<String>, false)
    };
}

/// Generates the predicate declaration + base/step Horn axioms for a single
/// transitive_closure! entry. The closure predicate is declared with the
/// same signature as the base (validated at runtime to be binary,
/// same-sort) and marked `cwa: true` so `finalize_completions` produces the
/// inductive definition.
macro_rules! transitive_closure_decl {
    // Entry with customization block.
    ($t:ident, $base:ident -> $closure:ident { $($field:ident : $val:expr),* $(,)? }) => {
        let $closure = transitive_closure_build!(
            $t, $base, $closure,
            { __nl: None::<&'static str>, __implicit: true },
            { $($field : $val),* }
        );
    };
    // Bare entry.
    ($t:ident, $base:ident -> $closure:ident) => {
        let $closure = transitive_closure_build!(
            $t, $base, $closure,
            { __nl: None::<&'static str>, __implicit: true },
            {}
        );
    };
}

/// Iterates over the customization fields, threading them into the
/// accumulator block; once empty, emits the declaration + axioms.
macro_rules! transitive_closure_build {
    // nl override.
    ($t:ident, $base:ident, $closure:ident,
        { __nl: $_nl:expr, __implicit: $imp:expr },
        { nl: $nl:expr $(, $($rest:tt)*)? }
    ) => {
        transitive_closure_build!(
            $t, $base, $closure,
            { __nl: Some($nl), __implicit: $imp },
            { $($($rest)*)? }
        )
    };
    // implicit override.
    ($t:ident, $base:ident, $closure:ident,
        { __nl: $nl:expr, __implicit: $_imp:expr },
        { implicit: $imp:expr $(, $($rest:tt)*)? }
    ) => {
        transitive_closure_build!(
            $t, $base, $closure,
            { __nl: $nl, __implicit: $imp },
            { $($($rest)*)? }
        )
    };
    // Customization exhausted — emit the actual declaration + axioms.
    ($t:ident, $base:ident, $closure:ident,
        { __nl: $nl:expr, __implicit: $imp:expr },
        {}
    ) => {{
        let __sig = $t.symbol($base).signature()
            .expect("transitive_closure: base must be a predicate");
        assert_eq!(__sig.params().len(), 2,
            "transitive_closure: base predicate must be binary");
        assert_eq!(__sig.params()[0], __sig.params()[1],
            "transitive_closure: base predicate must have both args of the same sort");
        let __sort = __sig.params()[0];
        let __nl_opt = $nl;
        let __closure_name = stringify!($closure);
        let __base_name = $t.symbol($base).name().to_string();

        let __closure_id = $t.declare_predicate(
            __closure_name,
            vec![__sort, __sort],
            __nl_opt,
            true,
        );

        // Base case: base(x, y) → closure(x, y)
        {
            let __v0 = $crate::theories::VarId(0);
            let __v1 = $crate::theories::VarId(1);
            let __vars = vec![(__v0, __sort), (__v1, __sort)];
            let __body = vec![$crate::theories::Atom::Predicate {
                symbol: $base,
                args: vec![$crate::theories::Term::Var(__v0), $crate::theories::Term::Var(__v1)],
            }];
            let __head = $crate::theories::Atom::Predicate {
                symbol: __closure_id,
                args: vec![$crate::theories::Term::Var(__v0), $crate::theories::Term::Var(__v1)],
            };
            let __kind = if $imp {
                $crate::theories::AxiomKind::Implicit
            } else {
                $crate::theories::AxiomKind::Explicit
            };
            let __meta = $crate::theories::AxiomMeta::new_raw(
                format!("{}_base", __closure_name),
                __kind,
                vec![],
            );
            $t.add_axiom(
                __meta,
                __vars,
                $crate::theories::AxiomBody::Horn { body: __body, head: __head },
            );
        }

        // Step case: closure(x, y) ∧ base(y, z) → closure(x, z)
        {
            let __v0 = $crate::theories::VarId(0);
            let __v1 = $crate::theories::VarId(1);
            let __v2 = $crate::theories::VarId(2);
            let __vars = vec![(__v0, __sort), (__v1, __sort), (__v2, __sort)];
            let __body = vec![
                $crate::theories::Atom::Predicate {
                    symbol: __closure_id,
                    args: vec![$crate::theories::Term::Var(__v0), $crate::theories::Term::Var(__v1)],
                },
                $crate::theories::Atom::Predicate {
                    symbol: $base,
                    args: vec![$crate::theories::Term::Var(__v1), $crate::theories::Term::Var(__v2)],
                },
            ];
            let __head = $crate::theories::Atom::Predicate {
                symbol: __closure_id,
                args: vec![$crate::theories::Term::Var(__v0), $crate::theories::Term::Var(__v2)],
            };
            let __kind = if $imp {
                $crate::theories::AxiomKind::Implicit
            } else {
                $crate::theories::AxiomKind::Explicit
            };
            let __meta = $crate::theories::AxiomMeta::new_raw(
                format!("{}_step", __closure_name),
                __kind,
                vec![],
            );
            $t.add_axiom(
                __meta,
                __vars,
                $crate::theories::AxiomBody::Horn { body: __body, head: __head },
            );
        }

        __closure_id
    }};
}

macro_rules! function_decl {
    ($t:ident, $func:ident, { ( $($param:ident),* $(,)? ) -> $ret:ident, nl: $nl:expr $(,)? }) => {
        $t.declare_function(stringify!($func), vec![$($param),*], $ret, Some($nl))
    };
    ($t:ident, $func:ident, { ( $($param:ident),* $(,)? ) -> $ret:ident $(,)? }) => {
        $t.declare_function(stringify!($func), vec![$($param),*], $ret, None::<String>)
    };
}

macro_rules! theory_stmt {
    // ------------------------------------------------------------------
    // preamble!(str)
    // ------------------------------------------------------------------
    ($t:ident, preamble ! ($text:expr)) => {
        $t.set_preamble($text);
    };

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
    // predicates!(
    //     p { (S1, S2), nl: "{0} ps {1}" },
    //     q { (S) },                       // no NL template
    //     ...
    // )
    //
    // Each entry's contents are captured as a single token tree and dispatched
    // to `predicate_decl!`, which has arms for the with-/without-`nl` forms.
    // ------------------------------------------------------------------
    ($t:ident, predicates ! ($($pred:ident $body:tt),* $(,)?)) => {
        $(
            #[allow(unused_variables)]
            let $pred = predicate_decl!($t, $pred, $body);
        )*
    };

    // ------------------------------------------------------------------
    // functions!(
    //     f { (S1, S2) -> R, nl: "..." },
    //     g { (S1) -> R },                 // no NL template
    //     ...
    // )
    // ------------------------------------------------------------------
    ($t:ident, functions ! ($($func:ident $body:tt),* $(,)?)) => {
        $(
            #[allow(unused_variables)]
            let $func = function_decl!($t, $func, $body);
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
    // transitive_closure!(
    //     base -> closure,
    //     base -> closure { nl: "...", implicit: false },
    //     ...
    // )
    //
    // Declares each closure predicate (cwa: true, same sort as base) and
    // emits its two Horn rules (base, step). With `cwa: true`, the
    // `finalize_completions` pass produces the inductive definition.
    // ------------------------------------------------------------------
    ($t:ident, transitive_closure ! (
        $($base:ident -> $closure:ident $({ $($field:ident : $val:expr),* $(,)? })?),* $(,)?
    )) => {
        $(
            transitive_closure_decl!($t, $base -> $closure $({ $($field : $val),* })?);
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
            body: $( $bsym:ident ( $($barg:ident),* $(,)? ) $(= $bval:ident)? ),+ $(,)? ;
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
                    horn_body_atom!( $bsym ( $($barg),* ) $(= $bval)? )
                ),+
            ];
            let __head = $crate::theories::Atom::Predicate {
                symbol: $hpred,
                args: vec![$( $crate::theories::Term::Var($harg) ),*],
            };
            let __implicit = if $implicit {
                $crate::theories::AxiomKind::Implicit
            } else {
                $crate::theories::AxiomKind::Explicit
            };
            let __meta = $crate::theories::AxiomMeta::new_nl($name, __implicit, $nl, vec![]);
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
            let __implicit = if $implicit {
                $crate::theories::AxiomKind::Implicit
            } else {
                $crate::theories::AxiomKind::Explicit
            };
            let __meta = $crate::theories::AxiomMeta::new_nl($name, __implicit, $nl, vec![]);
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
