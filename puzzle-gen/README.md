# Implicit theory puzzle generation

This is a generator for puzzles in an "implicit theory": a theory for which
certain axioms are taken to be "common knowledge". Such theories may or may not
be able to be fully explicated, but for some given implicit theory, the idea is
that we can delete certain axioms and still successfully solve the puzzle by
querying an LLM to recover the necessary axioms from the world theory.

As an example, consider the theory of corporate hierarchies. We might have
axioms defining how a "reports_to" relation might work, and how it relates to
"head_of_dept" or "can_fire" predicates. We _could_ in principle enumerate a
full theory of such hierarchies, but why do that when LLMs already know all
about how companies work? Why not let the model do the heavy lifting in the
theory-building process?
