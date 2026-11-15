import Lemma4.Spectral

namespace Lemma4

variable {n p : ℕ}

/-- The first inequality for arbitrary real design matrices and column selections. -/
theorem trace_pow_le_trace_sq_for_columns (X : Matrix (Fin n) (Fin p) ℝ)
    (A B : Finset (Fin p)) (r : ℕ) (hr : 2 ≤ r) :
    LinearMap.trace ℝ _ ((columnProjection X A - columnProjection X B) ^ r) ≤
      LinearMap.trace ℝ _ ((columnProjection X A - columnProjection X B) ^ 2) :=
  trace_pow_le_trace_sq (columnSpan X A) (columnSpan X B) r hr

/-- Combine the spectral inequality with a trace bound by the number of differing columns. -/
theorem lemma4_of_trace_sq_le (X : Matrix (Fin n) (Fin p) ℝ)
    (A B : Finset (Fin p)) (r : ℕ) (hr : 2 ≤ r)
    (hTraceBound :
      LinearMap.trace ℝ _ ((columnProjection X A - columnProjection X B) ^ 2) ≤
        ((A \ B).card : ℝ) + ((B \ A).card : ℝ)) :
    let D := columnProjection X A - columnProjection X B
    LinearMap.trace ℝ _ (D ^ r) ≤ LinearMap.trace ℝ _ (D ^ 2) ∧
      LinearMap.trace ℝ _ (D ^ 2) ≤ (A.card : ℝ) + (B.card : ℝ) - 2 * ((A ∩ B).card : ℝ) := by
  dsimp only
  refine ⟨trace_pow_le_trace_sq_for_columns X A B r hr, hTraceBound.trans ?_⟩
  have hA : ((A \ B).card : ℝ) + ((A ∩ B).card : ℝ) = A.card := by
    exact_mod_cast Finset.card_sdiff_add_card_inter A B
  have hB : ((B \ A).card : ℝ) + ((A ∩ B).card : ℝ) = B.card := by
    rw [Finset.inter_comm A B]
    exact_mod_cast Finset.card_sdiff_add_card_inter B A
  linarith

end Lemma4
