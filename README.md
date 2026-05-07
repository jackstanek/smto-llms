# SMTO with LLMs

This is an experimental project to look at incorporating "oracular reasoning"
with LLMs into SMT-based automated reasoning workflows. This repository is
divided into a few subdirectories:

- `puzzle-gen`: generator for logic puzzles which require "implicit theories" in
  order to solve. As written, the puzzles are underspecified and can't be solved
  directly by a solver; they require world knowledge of the application domain.
