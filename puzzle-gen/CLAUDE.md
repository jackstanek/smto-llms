# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project

Puzzle generator for the SMTO-with-LLM-oracle research project. Generates logic puzzles where part of the background theory is "implicit" (recoverable from an LLM oracle rather than stated in the puzzle). The first domain is workplace hierarchies (reporting, authority, expense approval). See `docs/design.md` for the full design document.

## Build and Check

```bash
cargo build          # build
cargo check          # type-check without codegen
cargo test           # run all tests
cargo test <name>    # run a single test by name
```

The nix devShell (`nix develop`) provides cvc5.

## Architecture

**Rust crate** (`src/`): The core IR and SMT backend live in `src/theories.rs`.

- **IR layer** — `Theory`, `Instance`, `Axiom`, `Formula`, `Term`, `Atom`. A `Theory` is a parameterized schema (sorts, symbols, axioms with Horn/integrity/general bodies). An `Instance` grounds a theory over finite domains with concrete facts and an ablatable axiom set (`active_axioms`). Axioms carry `vars: Vec<(VarId, SortId)>` for sort-annotated bound variables and `AxiomMeta` (implicit/explicit flag, category, NL template).
- **Backend trait** — `Backend` with `load_instance`, `assert_axiom` (incremental oracle recovery), and `check_entailment` (returns `Entailed`/`Refuted`/`Undetermined`).
- **SmtBackend** — `SmtBackend<'st, B>` borrows `&'st Storage` (caller-owned) to avoid self-referential lifetimes with `smtlib::Solver<'st, B>`. Translates the IR to SMT-LIB terms via the `smtlib` crate. Entailment uses push/pop scopes. Domain constants get `distinct` constraints.

**Reference theory** (`theories/workplace.smt`): Hand-written SMT-LIB2 encoding of the workplace theory with comments marking `implicit_by_default` flags. Serves as the ground-truth specification that the Rust IR should replicate.

## Key Dependencies

- `smtlib` (0.3.0) — high-level SMT-LIB interface; `Storage` is an arena that owns all SMT terms. The `'st` lifetime threads through `Solver`, `Bool`, `Dynamic`, etc.
- `slotmap` — typed slot-map keys (`SortId`, `SymbolId`, `AxiomId`) for the IR's internal registries.

## Important Patterns

- **Storage lifetime**: `SmtBackend` borrows `&'st Storage`; the caller must own the `Storage` and keep it alive. Typical usage: `let st = Storage::new(); let mut backend = SmtBackend::new(&st, z3)?;`
- **Entailment check**: Assert negated query in a push/pop scope. Unsat means entailed. This is standard SMT entailment, not closed-world minimal-model reasoning — the forward-chaining least-model computation for Horn theories is separate (not yet implemented).
- **Ablation**: `Instance::deactivate_axiom` removes axioms to test whether the oracle is needed. The generator invariant is that the explicit theory alone must *not* decide the query (otherwise the puzzle doesn't exercise the oracle).
