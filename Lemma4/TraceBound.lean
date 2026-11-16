/-
Lemma4/TraceBound.lean

Trace / dimension part of Lemma 4 of Shen, Pan, Zhu & Zhou (2013):

  Tr((P - Q)^2) = Tr P + Tr Q - 2 Tr(PQ)
  Tr(PQ) ≥ dim(K ⊓ L)
  Tr((P - Q)^2) ≤ dim K + dim L - 2 dim(K ⊓ L) ≤ |A| + |B| - 2|A ∩ B|

Everything is proved first for arbitrary symmetric projections `p q : E →ₗ[ℝ] E`
on a finite-dimensional real inner product space, then specialized to orthogonal
projections onto submodules, and finally to column spans of a real matrix `X`
(using `columnSpan` / `columnProjection` from `Lemma4.Defs`).
No rank assumption on `X` is needed.
-/
import Lemma4.Defs
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.Trace

open LinearMap Module

namespace Lemma4

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local notation "tr" => LinearMap.trace ℝ E

/-! ### Step 3: expanding the square -/

omit [FiniteDimensional ℝ E] in
/-- `Tr((p - q)^2) = Tr p + Tr q - 2 Tr(p q)` for idempotents `p`, `q`
(only `p^2 = p`, `q^2 = q` and cyclicity of the trace are used). -/
theorem trace_sub_sq {p q : E →ₗ[ℝ] E} (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) :
    tr ((p - q) ^ 2) = tr p + tr q - 2 * tr (p * q) := by
  have h : (p - q) ^ 2 = p * p - p * q - q * p + q * q := by
    rw [sq, sub_mul, mul_sub, mul_sub]; abel
  rw [h, hp.eq, hq.eq, map_add, map_sub, map_sub, LinearMap.trace_mul_comm ℝ q p]
  ring

/-- The trace of an idempotent operator is the dimension of its range. -/
theorem trace_eq_finrank_range {p : E →ₗ[ℝ] E} (hp : IsIdempotentElem p) :
    tr p = (finrank ℝ (range p) : ℝ) :=
  (IsIdempotentElem.isProj_range p hp).trace

/-- Range of the orthogonal projection onto `K`, viewed as a linear map, is `K`. -/
theorem range_starProjection_toLinearMap (K : Submodule ℝ E) :
    range (K.starProjection : E →ₗ[ℝ] E) = K := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact K.starProjection_apply_mem y
  · intro h
    exact ⟨x, Submodule.starProjection_eq_self_iff.mpr h⟩

/-! ### Step 4: `Tr(p q) ≥ dim(range p ⊓ range q)` -/

/-- For symmetric projections, `Tr(p q) ≥ 0`.
Proof: `Tr(p q) = Tr(p q p) = Σᵢ ‖q (p bᵢ)‖² ≥ 0` in an orthonormal basis `b`. -/
theorem trace_mul_nonneg {p q : E →ₗ[ℝ] E}
    (hp : p.IsSymmetricProjection) (hq : q.IsSymmetricProjection) : 0 ≤ tr (p * q) := by
  have hcyc : tr (p * q) = tr (p * q * p) := by
    conv_lhs => rw [← hp.isIdempotentElem.eq, mul_assoc]
    exact LinearMap.trace_mul_comm ℝ p (p * q)
  rw [hcyc, LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℝ E)]
  refine Finset.sum_nonneg fun i _ => ?_
  set b := stdOrthonormalBasis ℝ E i
  have : inner ℝ b ((p * q * p) b) = inner ℝ (q (p b)) (q (p b)) := by
    simp only [Module.End.mul_apply]
    calc inner ℝ b (p (q (p b))) = inner ℝ (p b) (q (p b)) := (hp.isSymmetric _ _).symm
      _ = inner ℝ (p b) (q (q (p b))) := by
          rw [← Module.End.mul_apply q q, hq.isIdempotentElem.eq]
      _ = inner ℝ (q (p b)) (q (p b)) := (hq.isSymmetric _ _).symm
  rw [this]
  exact real_inner_self_nonneg

omit [FiniteDimensional ℝ E] in
/-- If `r` is a symmetric projection whose range lies in the range of the
symmetric projection `q`, then `q r = r` and `r q = r`. -/
theorem mul_eq_of_range_le {q r : E →ₗ[ℝ] E}
    (hq : q.IsSymmetricProjection) (hr : r.IsSymmetricProjection) (h : range r ≤ range q) :
    q * r = r ∧ r * q = r := by
  have h1 : q * r = r := (hq.isIdempotentElem.comp_eq_right_iff r).mpr h
  refine ⟨h1, ?_⟩
  ext x
  refine ext_inner_left ℝ fun y => ?_
  rw [Module.End.mul_apply, ← hr.isSymmetric, ← hq.isSymmetric, ← Module.End.mul_apply, h1,
    hr.isSymmetric]

/-- **Step 4.** `Tr(p q) ≥ dim(range p ⊓ range q)` for symmetric projections.

Let `r` be the orthogonal projection onto `M = range p ⊓ range q`. Then
`p q - r = (p - r)(q - r)`, the two factors are symmetric projections, so
`Tr(p q) - Tr r = Tr((p - r)(q - r)) ≥ 0`, and `Tr r = dim M`. -/
theorem finrank_inf_le_trace_mul {p q : E →ₗ[ℝ] E}
    (hp : p.IsSymmetricProjection) (hq : q.IsSymmetricProjection) :
    (finrank ℝ (range p ⊓ range q : Submodule ℝ E) : ℝ) ≤ tr (p * q) := by
  set M : Submodule ℝ E := range p ⊓ range q
  set r : E →ₗ[ℝ] E := (M.starProjection : E →ₗ[ℝ] E)
  have hr : r.IsSymmetricProjection := M.isSymmetricProjection_starProjection
  have hrange : range r = M := range_starProjection_toLinearMap M
  have hrp : range r ≤ range p := hrange ▸ inf_le_left
  have hrq : range r ≤ range q := hrange ▸ inf_le_right
  obtain ⟨hpr, hrp'⟩ := mul_eq_of_range_le hp hr hrp
  obtain ⟨hqr, hrq'⟩ := mul_eq_of_range_le hq hr hrq
  have hfac : p * q = (p - r) * (q - r) + r := by
    rw [sub_mul, mul_sub, mul_sub, hpr, hrq', hr.isIdempotentElem.eq]; abel
  have hnn : 0 ≤ tr ((p - r) * (q - r)) :=
    trace_mul_nonneg (hr.sub_of_range_le_range hp hrp) (hr.sub_of_range_le_range hq hrq)
  rw [hfac, map_add, trace_eq_finrank_range hr.isIdempotentElem, hrange]
  linarith

/-! ### Abstract bound (Steps 3–4 combined) -/

/-- For symmetric projections `p`, `q`:
`Tr((p - q)^2) ≤ dim(range p) + dim(range q) - 2 dim(range p ⊓ range q)`. -/
theorem trace_sub_sq_le_of_isSymmetricProjection {p q : E →ₗ[ℝ] E}
    (hp : p.IsSymmetricProjection) (hq : q.IsSymmetricProjection) :
    tr ((p - q) ^ 2) ≤ (finrank ℝ (range p) : ℝ) + finrank ℝ (range q)
      - 2 * finrank ℝ (range p ⊓ range q : Submodule ℝ E) := by
  rw [trace_sub_sq hp.isIdempotentElem hq.isIdempotentElem,
    trace_eq_finrank_range hp.isIdempotentElem, trace_eq_finrank_range hq.isIdempotentElem]
  linarith [finrank_inf_le_trace_mul hp hq]

/-- **Steps 3–4 for subspaces.** With `P = projector K`, `Q = projector L` the orthogonal
projections onto `K`, `L`: `Tr((P - Q)^2) ≤ dim K + dim L - 2 dim(K ⊓ L)`. -/
theorem trace_sq_le (K L : Submodule ℝ E) :
    tr ((projector K - projector L) ^ 2)
      ≤ (finrank ℝ K : ℝ) + finrank ℝ L - 2 * finrank ℝ (K ⊓ L : Submodule ℝ E) := by
  have h := trace_sub_sq_le_of_isSymmetricProjection
    K.isSymmetricProjection_starProjection L.isSymmetricProjection_starProjection
  rw [range_starProjection_toLinearMap, range_starProjection_toLinearMap] at h
  exact h

/-! ### Step 5: counting dimensions for column spans -/

section Matrix

variable {n m : ℕ}

theorem columnSpan_mono (X : Matrix (Fin n) (Fin m) ℝ) {A B : Finset (Fin m)} (h : A ⊆ B) :
    columnSpan X A ≤ columnSpan X B :=
  Submodule.span_mono (Set.image_mono (by exact_mod_cast h))

/-- A span of at most `|A|` vectors has dimension at most `|A|`. -/
theorem finrank_columnSpan_le (X : Matrix (Fin n) (Fin m) ℝ) (A : Finset (Fin m)) :
    finrank ℝ (columnSpan X A) ≤ A.card := by
  classical
  unfold columnSpan
  rw [← Finset.coe_image]
  exact (finrank_span_finset_le_card _).trans Finset.card_image_le

/-- Adding the columns in `A \ B` to those in `A ∩ B` raises the dimension by at most
`|A \ B|`: `dim col(X_A) ≤ dim col(X_{A∩B}) + |A \ B|`. -/
theorem finrank_columnSpan_le_inter_add_sdiff (X : Matrix (Fin n) (Fin m) ℝ)
    (A B : Finset (Fin m)) :
    finrank ℝ (columnSpan X A) ≤ finrank ℝ (columnSpan X (A ∩ B)) + (A \ B).card := by
  classical
  have hsplit : columnSpan X A = columnSpan X (A ∩ B) ⊔ columnSpan X (A \ B) := by
    unfold columnSpan
    rw [← Submodule.span_union, ← Set.image_union]
    congr 2
    ext j
    simp only [Finset.coe_inter, Finset.coe_sdiff, Set.mem_union, Set.mem_inter_iff,
      Set.mem_sdiff, Finset.mem_coe]
    tauto
  rw [hsplit]
  exact (Submodule.finrank_add_le_finrank_add_finrank _ _).trans
    (Nat.add_le_add_left (finrank_columnSpan_le X _) _)

/-- **Step 5.** `dim K + dim L - 2 dim(K ⊓ L) ≤ |A \ B| + |B \ A|`
for `K = col(X_A)`, `L = col(X_B)`. -/
theorem dim_count_sdiff (X : Matrix (Fin n) (Fin m) ℝ) (A B : Finset (Fin m)) :
    (finrank ℝ (columnSpan X A) : ℝ) + finrank ℝ (columnSpan X B)
        - 2 * finrank ℝ (columnSpan X A ⊓ columnSpan X B : Submodule ℝ _)
      ≤ ((A \ B).card : ℝ) + (B \ A).card := by
  classical
  have hA := finrank_columnSpan_le_inter_add_sdiff X A B
  have hB := finrank_columnSpan_le_inter_add_sdiff X B A
  rw [Finset.inter_comm B A] at hB
  -- `col(X_{A∩B}) ⊆ col(X_A) ⊓ col(X_B)`
  have hC : finrank ℝ (columnSpan X (A ∩ B))
      ≤ finrank ℝ (columnSpan X A ⊓ columnSpan X B : Submodule ℝ _) :=
    Submodule.finrank_mono (le_inf (columnSpan_mono X Finset.inter_subset_left)
      (columnSpan_mono X Finset.inter_subset_right))
  have hA' : (finrank ℝ (columnSpan X A) : ℝ)
      ≤ finrank ℝ (columnSpan X (A ∩ B)) + (A \ B).card := by
    exact_mod_cast hA
  have hB' : (finrank ℝ (columnSpan X B) : ℝ)
      ≤ finrank ℝ (columnSpan X (A ∩ B)) + (B \ A).card := by
    exact_mod_cast hB
  have hC' : (finrank ℝ (columnSpan X (A ∩ B)) : ℝ)
      ≤ finrank ℝ (columnSpan X A ⊓ columnSpan X B : Submodule ℝ _) := by exact_mod_cast hC
  linarith

/-- **Second inequality of Lemma 4**, in the form `Main.lean` takes as `hTraceBound`:
for any real matrix `X` (no rank assumption) and column subsets `A`, `B`,
`Tr((P_A - P_B)^2) ≤ |A \ B| + |B \ A|`. -/
theorem trace_sq_le_card_sdiff (X : Matrix (Fin n) (Fin m) ℝ) (A B : Finset (Fin m)) :
    LinearMap.trace ℝ _ ((columnProjection X A - columnProjection X B) ^ 2)
      ≤ ((A \ B).card : ℝ) + ((B \ A).card : ℝ) :=
  (trace_sq_le (columnSpan X A) (columnSpan X B)).trans (dim_count_sdiff X A B)

/-- **Second inequality of Lemma 4**, in the paper's form:
`Tr((P_A - P_B)^2) ≤ |A| + |B| - 2|A ∩ B|`. -/
theorem trace_sq_le_card (X : Matrix (Fin n) (Fin m) ℝ) (A B : Finset (Fin m)) :
    LinearMap.trace ℝ _ ((columnProjection X A - columnProjection X B) ^ 2)
      ≤ (A.card : ℝ) + B.card - 2 * (A ∩ B).card := by
  have h := trace_sq_le_card_sdiff X A B
  have cA : ((A \ B).card : ℝ) + (A ∩ B).card = A.card := by
    exact_mod_cast Finset.card_sdiff_add_card_inter A B
  have cB : ((B \ A).card : ℝ) + (A ∩ B).card = B.card := by
    rw [Finset.inter_comm A B]
    exact_mod_cast Finset.card_sdiff_add_card_inter B A
  linarith

end Matrix

end Lemma4
