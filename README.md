# Trace Powers of Orthogonal Projection Differences

This Lean 4 project formalizes the first inequality in Lemma 4 of Shen, Pan, Zhu, and Zhou (2013). For two sets of columns of a real matrix, let `P` and `Q` be the orthogonal projections onto their spans. The theorem bounds the trace of `(P - Q)^r` by the trace of `(P - Q)^2` for every natural number `r ≥ 2`. It applies to arbitrary real matrices, including rank-deficient column selections. [Original paper](https://doi.org/10.1007/s10463-012-0396-3)

## Build

Run the following from the project root with Lean managed by Elan. The toolchain and manifest pin Lean and Mathlib to reproducible versions.

```sh
lake exe cache get \
  Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional \
  Mathlib.Analysis.InnerProductSpace.Spectrum \
  Mathlib.LinearAlgebra.Trace \
  Mathlib.Tactic.Linarith
lake build
```

## Definitions and theorems

| File | Contents |
| --- | --- |
| `Lemma4/Defs.lean` | `projector`, `columnVector`, `columnSpan`, and `columnProjection`, in the namespace `Lemma4` |
| `Lemma4/Spectral.lean` | `trace_pow_le_trace_sq` for two subspaces of a finite-dimensional real inner-product space |
| `Lemma4/Main.lean` | `trace_pow_le_trace_sq_for_columns` for a real design matrix, and `lemma4_of_trace_sq_le` to combine the two inequalities |

## Connect the trace bound

Import `Lemma4.Defs` and `Mathlib.LinearAlgebra.Trace` for the trace and dimension proof. The common ambient space is `EuclideanSpace ℝ (Fin n)`, and every projection is a linear endomorphism of that space. With `open Lemma4`, the required conclusion for `X : Matrix (Fin n) (Fin p) ℝ` and `A B : Finset (Fin p)` is

```lean
LinearMap.trace ℝ _ ((columnProjection X A - columnProjection X B) ^ 2) ≤
  ((A \ B).card : ℝ) + ((B \ A).card : ℝ)
```

Pass this proof as `hTraceBound` to `lemma4_of_trace_sq_le X A B r hr`. The assembly theorem then gives the two inequalities with the cardinality bound written in the paper's form, `|A| + |B| - 2 |A ∩ B|`.

## Proof dependencies

The spectral proof works with finite-dimensional real inner-product spaces. Each orthogonal projection has a quadratic form in `[0, 1]` on unit vectors. For a unit eigenvector of the difference, subtracting the two quadratic forms bounds its eigenvalue in `[-1, 1]`. Diagonalization expresses each trace as a sum of powers, and the scalar inequality holds term by term.

`#print axioms` on `Lemma4.trace_pow_le_trace_sq_for_columns` and `Lemma4.lemma4_of_trace_sq_le` lists `propext`, `Classical.choice`, and `Quot.sound`. The assembly theorem takes the second inequality as an explicit proof argument.
