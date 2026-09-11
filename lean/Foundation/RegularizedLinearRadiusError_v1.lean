import LinearRadiusLimits_v1

noncomputable section
namespace TheoremT.Continuum

theorem regularizedLinearRadius_sub_norm_bound {N : ℕ} (A : Configuration N →L[ℝ] Position)
    {δ : ℝ} (hδ : 0 < δ) (x : Configuration N) :
    |regularizedLinearRadius A δ x-‖A x‖| ≤ Real.sqrt δ := by
  rw [abs_of_nonneg (sub_nonneg.mpr (norm_le_regularizedLinearRadius A hδ x))]
  have hs := Real.sq_sqrt hδ.le
  have hr := regularizedLinearRadius_sq A hδ x
  have hpos := regularizedLinearRadius_pos A hδ x
  have hnorm := norm_nonneg (A x)
  have hsq := Real.sqrt_nonneg δ
  nlinarith

#print axioms regularizedLinearRadius_sub_norm_bound
end TheoremT.Continuum
