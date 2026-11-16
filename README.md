# Trace Powers of Orthogonal Projection Differences

This Lean 4 project formalizes both inequalities in Lemma 4 of Shen, Pan, Zhu, and Zhou (2013). Let $P_A$ and $P_B$ be the orthogonal projections onto the spans of the columns of a real matrix $X$ indexed by $A$ and $B$. For every natural number $r \ge 2$, `Lemma4.lemma4_main` proves

```text
tr((P_A - P_B)^r) ≤ tr((P_A - P_B)^2) ≤ |A| + |B| - 2|A ∩ B|
```

The theorem applies to arbitrary real matrices, including rank-deficient column selections. [Original paper](https://doi.org/10.1007/s10463-012-0396-3)

## Build

Run the following from the project root with Lean managed by Elan. The toolchain file and dependency manifest pin Lean and Mathlib to `v4.31.0`.

```sh
lake exe cache get \
  Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional \
  Mathlib.Analysis.InnerProductSpace.Spectrum \
  Mathlib.Analysis.InnerProductSpace.Trace \
  Mathlib.LinearAlgebra.Trace \
  Mathlib.Tactic.Linarith
lake build
```

## Definitions and theorems

| File | Contents |
| --- | --- |
| [Lemma4/Defs.lean](Lemma4/Defs.lean) | Defines `projector`, `columnVector`, `columnSpan`, and `columnProjection`. |
| [Lemma4/Spectral.lean](Lemma4/Spectral.lean) | Proves the first inequality in `trace_pow_le_trace_sq`. |
| [Lemma4/TraceBound.lean](Lemma4/TraceBound.lean) | Proves the second inequality in `trace_sq_le_card_sdiff`. |
| [Lemma4/Main.lean](Lemma4/Main.lean) | Combines the two results in `lemma4_main` and expresses the cardinality bound in the paper's form. |

The spectral proof bounds the eigenvalues of the projection difference in $[-1,1]$ and compares their powers term by term. The trace proof expands the square and uses the dimension of the subspace intersection as a lower bound on the trace of the product. A count of the differing column indices then bounds the resulting dimension expression.

## Verify the main theorem

After building, run the following to check the theorem statement and its axiom dependencies.

```sh
lake env lean --stdin <<'LEAN'
import Lemma4

#check Lemma4.lemma4_main
#print axioms Lemma4.lemma4_main
LEAN
```

The axiom check lists Lean's standard axioms `propext`, `Classical.choice`, and `Quot.sound`.
