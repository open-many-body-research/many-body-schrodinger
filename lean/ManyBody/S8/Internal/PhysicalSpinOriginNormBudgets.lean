import CoulombSpinLocallyLipschitz_v1

/-! Original-state bounds for the literal finite-spin origin amplitude and
    the source/H12 budget expressions. No derivative or PDE budget is input. -/
noncomputable section
open scoped NNReal BigOperators
namespace ManyBody.S8
open TheoremT.Continuum

/-- The physical spin Moser estimate controls the full square sum at the origin. -/
theorem spin_origin_sum_sq_original_norm_le {N : ℕ} {Z E : ℝ} {ψ : SpinSpace N}
    {u : SpinConfiguration N → Configuration N → ℂ}
    (hm : ∀ x, Real.sqrt (∑ σ : SpinConfiguration N, ‖u σ x‖^2) ≤
      coulombMoserBoundCoefficient N Z E * ‖ψ‖) :
    (∑ σ : SpinConfiguration N, ‖u σ 0‖^2) ≤
      (coulombMoserBoundCoefficient N Z E)^2 * ‖ψ‖^2 := by
  have hs : 0 ≤ ∑ σ : SpinConfiguration N, ‖u σ 0‖^2 :=
    Finset.sum_nonneg fun σ _ => sq_nonneg _
  have hb := pow_le_pow_left₀ (Real.sqrt_nonneg _) (hm 0) 2
  rwa [Real.sq_sqrt hs, mul_pow] at hb

/-- The actual square-root origin source amplitude has a linear original-state bound. -/
theorem spin_origin_source_original_norm_le {N : ℕ} {Z E : ℝ} {ψ : SpinSpace N}
    {u : SpinConfiguration N → Configuration N → ℂ} {M V : ℝ} (hM : 0 ≤ M)
    (hm : ∀ x, Real.sqrt (∑ σ : SpinConfiguration N, ‖u σ x‖^2) ≤
      coulombMoserBoundCoefficient N Z E * ‖ψ‖) :
    M * Real.sqrt (∑ σ : SpinConfiguration N, ‖u σ 0‖^2) * Real.sqrt V ≤
      (M * coulombMoserBoundCoefficient N Z E * Real.sqrt V) * ‖ψ‖ := by
  have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hm 0) hM)
    (Real.sqrt_nonneg V)
  calc
    _ ≤ M * (coulombMoserBoundCoefficient N Z E * ‖ψ‖) * Real.sqrt V := hb
    _ = _ := by ring

/-- Choosing the genuine local Lipschitz constant as C times the original norm
    turns the literal origin H12 budget into a quadratic original-state bound. -/
theorem spin_origin_h12_original_norm_le {N : ℕ} {Z E : ℝ} {ψ : SpinSpace N}
    {u : SpinConfiguration N → Configuration N → ℂ} (C : ℝ≥0) {C_H : ℝ}
    (hCH : 0 ≤ C_H)
    (hm : ∀ x, Real.sqrt (∑ σ : SpinConfiguration N, ‖u σ x‖^2) ≤
      coulombMoserBoundCoefficient N Z E * ‖ψ‖) :
    (((C * ‖ψ‖₊ : ℝ≥0) : ℝ)^2 + ∑ σ : SpinConfiguration N, ‖u σ 0‖^2) * C_H ≤
      (C_H * ((C : ℝ)^2 + (coulombMoserBoundCoefficient N Z E)^2)) * ‖ψ‖^2 := by
  calc
    _ ≤ (((C * ‖ψ‖₊ : ℝ≥0) : ℝ)^2 +
        (coulombMoserBoundCoefficient N Z E)^2 * ‖ψ‖^2) * C_H :=
      mul_le_mul_of_nonneg_right
        (add_le_add le_rfl (spin_origin_sum_sq_original_norm_le hm)) hCH
    _ = _ := by
      simp only [NNReal.coe_mul, coe_nnnorm]
      ring

#print axioms spin_origin_sum_sq_original_norm_le
#print axioms spin_origin_source_original_norm_le
#print axioms spin_origin_h12_original_norm_le
end ManyBody.S8
