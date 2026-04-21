# Puzzle Generator Design

A living design document for the SMTO-with-LLM-oracle puzzle generator. This
document covers the conceptual framing (implicit vs. explicit theory,
adequacy, ablation), the generation pipeline, and the evaluation methodology.
Implementation details (the Rust IR, SMT-LIB emission, oracle plumbing) live
in separate documents.

---

## 1. Core Concepts

### 1.1 The role of a theory

A **theory** $T$ is a set of axioms over a signature (sorts, predicates,
functions) that pins down the meaning of the domain's vocabulary. For a
puzzle domain (workplace relationships, kinship, clinical eligibility, etc.),
$T$ captures the relationships that competent humans take for granted: that
reporting propagates company membership, that a department head works in
that department, that self-approval of expenses is forbidden.

A **puzzle instance** is a tuple $(F, Q)$ where $F$ is a set of ground facts
and $Q$ is a query. The intended answer to the puzzle is determined by $T
\cup F$: specifically, whether $T \cup F \models Q$, whether $T \cup F
\models \neg Q$, or whether $Q$ is undetermined under $T \cup F$.

The insight driving this generator is that **the theory is never shown to
the solver in its entirety**. Some axioms are stated in the puzzle text;
others are left implicit and must be recovered from the LLM oracle during
solving. This lets us generate puzzles where a pure SMT solver cannot
succeed without oracle queries, and where the identity of the *recovered*
axioms is a measurable experimental quantity.

### 1.2 Implicit vs. explicit theory

Each axiom in $T$ carries a boolean flag `implicit_by_default`. This reflects
whether a competent human reading the puzzle would expect the axiom to be
stated (*explicit*) or would take it for granted (*implicit*).

- **Explicit axioms** are rendered into the puzzle text as natural-language
  rules ("Alice's expense report was approved by Bob").
- **Implicit axioms** are withheld from the puzzle text. They belong to the
  background theory the oracle is expected to know — things like "reporting
  propagates company membership" or "one cannot approve one's own expenses."

The split is a *design-time* judgment about domain norms, not a fixed
property of the axiom. For ablation studies, the generator can override the
default: making implicit axioms explicit (to measure how much the oracle
helps at all) or making explicit axioms implicit (to stress-test oracle
coverage).

### 1.3 Adequacy for a query class

A theory is **adequate for a query class $\mathcal{Q}$** iff for every
well-formed instance $(F, q)$ with $q \in \mathcal{Q}$, either $T \cup F
\models q$ or $T \cup F \models \neg q$. This is a weaker property than
proof-theoretic completeness: $T$ need not decide every sentence in its
language, only those arising from the puzzle's query distribution.

Adequacy is a property we *design for*, not one we assume. The generator's
job is to produce instances where the theory is adequate — no ambiguous
puzzles — so that ground truth is well-defined. Adequacy failures during
generation are bugs in the theory or the sampler and should be detected
automatically (see §3.2).

### 1.4 Finite categoricity per instance

For any given puzzle instance, the entity set is finite and enumerated. We
further require that $T \cup F$ admit a unique extension to a complete
structure over those entities — the **intended model**. This is finite
categoricity over the instance's domain. It makes the answer to every query
unambiguous and gives us a canonical ground truth against which to evaluate
both symbolic solvers and LLM-based approaches.

Under closed-world reasoning for Horn-shaped theories, the least Herbrand
model serves as the intended model directly. For richer theories, the
generator must explicitly check that only one completion is consistent with
$F$.

### 1.5 Axiom ablation

**Ablation** is the operation of removing a subset of axioms from the theory
visible to the solver. The generator produces puzzles by:

1. Starting from the full theory $T$.
2. Removing (at least) all axioms tagged `implicit_by_default`.
3. Optionally removing additional axioms for difficulty scaling.
4. Handing the solver the reduced theory $T' \subseteq T$ together with $F$
   and $Q$.

The solver's task is to use the oracle to recover enough of $T \setminus T'$
to determine $Q$. We say the oracle has **recovered** an axiom if the solver
asserts a semantically equivalent formula based on oracle responses.
Tracking which axioms were recovered yields a per-instance **recovery set**,
which supports several experimental measures (§3).

### 1.6 Oracle as a late-binding knowledge source

Unlike approaches that translate a full problem to SMT-LIB in one shot
(SAT-LM, LogicLM), this generator assumes the solver invokes the oracle
*during* search, in response to concrete solver state. Oracle calls are
narrow: given a specific predicate instance the solver is stuck on, the
oracle supplies either a ground implication or a universally-quantified
Horn-shaped fragment. Responses enter the solver's assumption set rather
than the theory proper, so inconsistent oracle responses can be detected
and reconciled (CEGAR-style) rather than silently corrupting the search.

This late-binding property is what makes implicit/explicit theory a
meaningful distinction in the first place: a one-shot approach must decide
upfront what vocabulary to formalize, whereas an interactive solver asks
only what it needs.

---

## 2. The Generation Pipeline

A puzzle instance is produced by the following pipeline. Each stage is
independently configurable and testable.

### 2.1 Sample instance structure

Given a theory schema (sorts and predicates), sample a concrete domain:

- **Entity counts** per sort (e.g., 4 employees, 2 departments, 1 company).
- **Structural shape** for any relations that carry structural constraints
  (e.g., the reporting tree: shape, depth, branching factor).
- **Assignments** for functional relations (e.g., each employee's department
  and company).

The sampler is parameterized by **difficulty axes** (§3.3). Structural
sampling should produce a well-formed structure: no reporting cycles, no
department without a company, etc. Ill-formed samples are rejected and
resampled.

### 2.2 Derive the ground-truth model

With the sampled structure fixed, compute the least model of $T$ over this
domain: the closure of the sampled ground facts under the full theory. This
is the **intended model** $M^\star$. Every atomic query has a determinate
answer in $M^\star$.

For Horn theories, least-model computation is a forward-chaining fixed
point. For extensions (stratified negation, aggregation), use the
corresponding evaluation semantics.

### 2.3 Select a query

Sample a query $q$ from the target query distribution $\mathcal{Q}$. The
query distribution is a design choice — typical options:

- **Entailment queries** ("can Dave fire Alice?"): atomic, with Yes/No
  answers read off $M^\star$.
- **Counting queries** ("how many people can Dave fire?"): aggregate, with
  numeric answers.
- **Existence queries** ("is there someone who can fire Alice?"):
  existential, with Yes/No answers.
- **Coherence queries** ("is it consistent that Alice approved Charlie's
  expenses?"): answered by checking whether $F \cup \{q\}$ admits any model.

The query's intended answer is recorded alongside the instance.

### 2.4 Partition explicit and implicit axioms

Compute the axiom partition:

- **Explicit axioms** $T_{\text{exp}}$: those tagged
  `implicit_by_default = false`, plus any axioms overridden to explicit for
  this instance.
- **Implicit axioms** $T_{\text{imp}}$: everything else.

Only $T_{\text{exp}}$ will be rendered into the puzzle text.
$T_{\text{imp}}$ is the set the oracle is expected to cover.

### 2.5 Render the puzzle

Produce a natural-language rendering:

- Each ground fact in $F$ is rendered as a sentence.
- Each explicit axiom in $T_{\text{exp}}$ is rendered as a rule statement.
- The query $q$ is rendered as a question.

Rendering uses per-axiom and per-predicate templates defined alongside the
formal theory. Rendering should be idempotent and reversible: given the
rendered text plus the theory schema, it should be possible to reconstruct
the underlying formal instance.

### 2.6 Package the instance

Emit a structured record containing:

- The rendered NL puzzle (for LLM baselines).
- The formal instance: sorts, domain, $F$, $q$, $T_{\text{exp}}$ (for
  symbolic solvers).
- Ground truth: the answer, the full $T$, and the set of axioms that would
  need to be recovered to derive the answer.
- Metadata: difficulty parameters, random seed, generator version.

---

## 3. Evaluation Methodology

### 3.1 Baselines

The puzzle is evaluated against the following systems, in order of
increasing sophistication:

1. **Raw LLM** (chain-of-thought prompting): reads the NL puzzle, reasons
   directly, outputs an answer. Measures the LLM's native capability.
2. **Raw LLM with self-consistency**: samples multiple CoT traces, takes
   majority vote. Controls for CoT variance.
3. **SAT-LM / LogicLM**: LLM produces a single declarative formalization
   of the problem, which is handed to a SAT/SMT solver. The critical
   baseline — *this is what the framework must beat*.
4. **SMTO-with-LLM-oracle** (the system under test): solver is handed
   $T_{\text{exp}}$, $F$, $q$; uses the LLM as an oracle during search to
   recover pieces of $T_{\text{imp}}$ as needed.

### 3.2 Generator invariants (to check, not to measure)

Before evaluation, every generated instance must satisfy:

- **Adequacy**: $T \cup F$ decides $q$.
- **Finite categoricity**: $T \cup F$ has a unique model over the instance
  domain.
- **Explicit-theory insufficiency**: $T_{\text{exp}} \cup F$ does *not*
  decide $q$. (If it does, the puzzle doesn't exercise the oracle and is
  not informative.)
- **Full-theory determinacy**: $T \cup F \models q$ or $T \cup F \models
  \neg q$, matching the recorded ground truth.

These are automated pre-flight checks. Instances that fail any invariant
are discarded.

### 3.3 Difficulty axes

Controlled axes over which to generate instance batches:

- **Chain depth $d$**: the number of axiom applications required to derive
  $q$ from $F$ under $T$. Primary difficulty axis; raw-LLM performance
  degrades predictably with $d$.
- **Entity count $n$**: size of the sort domains. Controls whether the
  problem fits in working memory for a one-shot LLM.
- **Relation variety $r$**: number of distinct predicate symbols used in
  $F$ and $q$. Controls the breadth of theory recovery required.
- **Trap density $t$**: fraction of plausible-but-false rules suggested by
  $F$'s surface form but *not* entailed by $T$. Specifically measures
  whether soundness recovery catches oracle errors.
- **Ambiguity budget $a$** (if the generator supports ambiguous
  instances): fraction of instances where $q$ is undetermined under $T
  \cup F$, with the expected answer being "unknown." Tests whether the
  system distinguishes unknown from false.

The headline experiment is a 2D grid, typically over $(d, n)$ or $(d, t)$,
with each cell containing enough instances for statistical comparison
between baselines.

### 3.4 Metrics

For each baseline and each instance, record:

- **Accuracy**: did the system produce the correct answer?
- **Calibration**: if the system reports confidence or can say "unknown,"
  did its confidence correlate with correctness? Distinguishes systems that
  know their limits from those that hallucinate confidently.
- **Oracle query count** (SMTO only): how many oracle calls were made.
- **Recovery fraction** (SMTO only): $|\text{recovered axioms}| /
  |T_{\text{imp needed}}|$, where $T_{\text{imp needed}}$ is the subset of
  $T_{\text{imp}}$ actually used in the ground-truth derivation.
- **Inconsistency detection rate** (SMTO only): fraction of instances in
  which the assumption set became unsatisfiable during solving, prompting a
  re-query.
- **Latency and cost**: wall-clock and oracle-API cost per instance.

The recovery fraction is the metric *unique to the SMTO-with-oracle
framework*. No baseline can report it — SAT-LM either encodes a rule or
doesn't, with no notion of partial recovery. This is the quantity to
foreground in writeups.

### 3.5 Headline claim to support

The evaluation is designed to support, or refute, claims of the form:

> At moderate-to-high difficulty, SMTO-with-LLM-oracle attains higher
> accuracy than SAT-LM while recovering only a fraction of the full
> background theory — demonstrating that late-binding theory recovery is
> both possible and efficient.

If this claim fails — for example, if SAT-LM dominates at every generatable
difficulty — the evaluation should make the failure mode visible (is the
theory too small? is the domain too narrow? is the LLM strong enough to
one-shot everything?), so that either the generator is rescaled or the
scope of the claim is narrowed.

### 3.6 Secondary experiments

Beyond the headline grid, the generator supports several follow-up
experiments cheaply:

- **Trap-density ablation**: vary $t$ at fixed $d$, measure how SAT-LM's
  accuracy degrades (it incorporates incorrect rules from the LLM's
  formalization) versus SMTO's accuracy (it catches inconsistencies).
- **Explicit-vs-implicit sensitivity**: vary which axioms are marked
  implicit, measure how recovery fraction and accuracy move. Validates
  that the implicit/explicit split captures something meaningful.
- **Oracle-quality ablation**: replace the LLM with weaker models (smaller
  parameter counts, older generations) to trace how performance degrades
  with oracle quality.
- **Cross-domain transfer** (once multiple theories are implemented):
  prompt the oracle with few-shot examples from domain A and evaluate on
  domain B, measuring how well oracle reasoning generalizes.

---

## 4. Domain instantiation

The first domain is a workplace-relationships theory with sorts for
employees, departments, and companies; structural relations (reports-to,
head-of, department-of); and authority predicates derived from structure
(can-fire, can-approve-expense). Puzzles ask about authority and act
coherence, with difficulty scaled by chain depth and org size.

Subsequent domains (taxonomic/kinship reasoning, statutory eligibility,
clinical guideline application) instantiate the same pipeline with
different theories and render templates. The pipeline is domain-agnostic:
only the theory, the entity samplers, and the NL templates change.
