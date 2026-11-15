import Lemma4.Defs
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.Trace
import Mathlib.Tactic.Linarith

open scoped BigOperators RealInnerProductSpace

namespace Lemma4

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

private theorem inner_projector_unit_bounds (K : Submodule ℝ E) {v : E}
    (hv : ‖v‖ = 1) : 0 ≤ ⟪projector K v, v⟫ ∧ ⟪projector K v, v⟫ ≤ 1 := by
  have hinner : ⟪projector K v, v⟫ = ‖K.orthogonalProjectionOnto v‖ ^ 2 := by
    simpa [projector] using K.re_inner_starProjection_eq_normSq v
  have hnorm : ‖K.orthogonalProjectionOnto v‖ ≤ 1 := by
    simpa [hv] using K.norm_orthogonalProjectionOnto_apply_le v
  rw [hinner]
  refine ⟨sq_nonneg _, ?_⟩
  simpa using pow_le_pow_left₀ (norm_nonneg _) hnorm 2

private theorem trace_pow_eq_sum_eigenvalues {D : E →ₗ[ℝ] E} (hD : D.IsSymmetric)
    (s : ℕ) :
    LinearMap.trace ℝ E (D ^ s) = ∑ i, (hD.eigenvalues rfl i) ^ s := by
  let b := (hD.eigenvectorBasis rfl).toBasis
  have hdiag : LinearMap.toMatrix b b D = Matrix.diagonal (hD.eigenvalues rfl) := by
    simpa [b] using hD.toMatrix_eigenvectorBasis rfl
  have hpow : LinearMap.toMatrix b b (D ^ s) = (LinearMap.toMatrix b b D) ^ s :=
    map_pow (LinearMap.toMatrixAlgEquiv b) D s
  rw [LinearMap.trace_eq_matrix_trace ℝ b, hpow, hdiag, Matrix.diagonal_pow,
    Matrix.trace_diagonal]
  simp only [Pi.pow_apply]

/-- The first inequality in Lemma 4, for a difference of orthogonal projections. -/
theorem trace_pow_le_trace_sq (K L : Submodule ℝ E) (r : ℕ) (hr : 2 ≤ r) :
    LinearMap.trace ℝ E ((projector K - projector L) ^ r) ≤
      LinearMap.trace ℝ E ((projector K - projector L) ^ 2) := by
  let D : E →ₗ[ℝ] E := projector K - projector L
  have hD : D.IsSymmetric := (projector_isSymmetric K).sub (projector_isSymmetric L)
  let basis := hD.eigenvectorBasis rfl
  have heigen (i : Fin (Module.finrank ℝ E)) : |hD.eigenvalues rfl i| ≤ 1 := by
    let v := basis i
    have hv : ‖v‖ = 1 := basis.orthonormal.norm_eq_one i
    have hDv : D v = (hD.eigenvalues rfl i) • v :=
      hD.apply_eigenvectorBasis rfl i
    have heq : hD.eigenvalues rfl i = ⟪projector K v, v⟫ - ⟪projector L v, v⟫ := by
      calc
        _ = ⟪D v, v⟫ := by
          rw [hDv, real_inner_smul_left, real_inner_self_eq_norm_sq, hv]
          simp
        _ = _ := by simp only [D, LinearMap.sub_apply, inner_sub_left]
    have hK := inner_projector_unit_bounds K hv
    have hL := inner_projector_unit_bounds L hv
    rw [heq, abs_le]
    exact ⟨by linarith [hK.1, hL.2], by linarith [hK.2, hL.1]⟩
  change LinearMap.trace ℝ E (D ^ r) ≤ LinearMap.trace ℝ E (D ^ 2)
  rw [trace_pow_eq_sum_eigenvalues hD r, trace_pow_eq_sum_eigenvalues hD 2]
  apply Finset.sum_le_sum
  intro i _
  let eigenvalue := hD.eigenvalues rfl i
  change eigenvalue ^ r ≤ eigenvalue ^ 2
  calc
    eigenvalue ^ r ≤ |eigenvalue| ^ r := by
      simpa only [abs_pow] using le_abs_self (eigenvalue ^ r)
    _ ≤ |eigenvalue| ^ 2 := pow_le_pow_of_le_one (abs_nonneg _) (heigen i) hr
    _ = eigenvalue ^ 2 := sq_abs eigenvalue

end Lemma4
