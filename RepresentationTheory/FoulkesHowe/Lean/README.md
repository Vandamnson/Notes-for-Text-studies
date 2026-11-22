# Quadratic stabilization of the canonical Foulkes–Howe map

The theorem `OAI.Problem346.canonical_foulkes_howe_surjective` establishes surjectivity of the canonical map for finite-dimensional complex vector spaces when `2 ≤ a` and `a * (a - 1) ≤ b`. [Lean statement and proof](OAI/RepresentationTheory/FoulkesHowe/Stabilization.lean) · [Working notes](../foulkes_howe_notes.pdf)

The 78 modules under `OAI/` are reproduced from [OpenAI’s formalization at revision 4eaee875](https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/RepresentationTheory/FoulkesHowe) under its [Apache 2.0 license](LICENSE). The local [end-to-end check](EndToEnd.lean) connects the statement to Mathlib homogeneous polynomials and the pure-power formula. [Audit.lean](Audit.lean) inspects the statements and their axioms.

With Elan installed, run these commands from this directory. The project pins Lean 4.34.1 and the Mathlib revision used for verification.

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```
