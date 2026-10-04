import ExteriorExponentialWeights_v1

/-! Uniform squared-gradient bound for the actual exterior exponential weights.
The right side is independent of the saturation cap L. -/
noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum

def exteriorWeightError (N : ℕ) (R a C : ℝ) : ℝ :=
  (Fintype.card (Coordinate N) : ℝ) * ((C/R)*Real.exp (a*(2*R+1)))^2

theorem cutoff_derivative_times_weight_abs_le {N : ℕ} {R a L C : ℝ}
    (hR : 0 < R) (ha : 0 ≤ a) (hL : 0 < L) (hC : 0 ≤ C)
    (hcut : ∀ (x : Configuration N) (k : Coordinate N),
      ‖fderiv ℝ (scaledCutoff N R) x (coordinateVector k)‖ ≤ C/R)
    (x : Configuration N) (k : Coordinate N) :
    |fderiv ℝ (scaledCutoff N R) x (coordinateVector k) * boundedExpWeight N a L x| ≤
      (C/R)*Real.exp (a*(2*R+1)) := by
  by_cases hx : ‖x‖ ≤ 2*R
  · rw [abs_mul,abs_of_pos (boundedExpWeight_pos N a hL x)]
    have hw : boundedExpWeight N a L x ≤ Real.exp (a*(2*R+1)) := by
      apply (boundedExpWeight_le_exp N a hL x).trans
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left
        ((smoothConfigurationRadius_le_norm_add_one x).trans (by linarith)) ha
    exact mul_le_mul (by simpa only [Real.norm_eq_abs] using hcut x k) hw
      (boundedExpWeight_pos N a hL x).le (div_nonneg hC hR.le)
  · rw [scaledCutoff_partial_eq_zero_of_two_mul_lt hR (lt_of_not_ge hx) k,
      zero_mul,abs_zero]
    positivity

theorem exteriorExpWeight_gradient_bound {N : ℕ} {R a L C : ℝ}
    (hR : 0 < R) (ha : 0 ≤ a) (hL : 0 < L) (hC : 0 ≤ C)
    (hcut : ∀ (x : Configuration N) (k : Coordinate N),
      ‖fderiv ℝ (scaledCutoff N R) x (coordinateVector k)‖ ≤ C/R)
    (x : Configuration N) :
    (1/2 : ℝ) * (∑ k : Coordinate N,
      (fderiv ℝ (exteriorExpWeight N R a L) x (coordinateVector k))^2) ≤
      a^2*(exteriorExpWeight N R a L x)^2 + exteriorWeightError N R a C := by
  have hpoint (k : Coordinate N) :
      (fderiv ℝ (exteriorExpWeight N R a L) x (coordinateVector k))^2 ≤
      2*(exteriorTaper N R x)^2*(fderiv ℝ (boundedExpWeight N a L) x (coordinateVector k))^2 +
        2*((C/R)*Real.exp (a*(2*R+1)))^2 := by
    rw [exteriorExpWeight_partial R a hL]
    have hb := cutoff_derivative_times_weight_abs_le hR ha hL hC hcut x k
    have hs := pow_le_pow_left₀ (abs_nonneg _) hb 2
    rw [sq_abs] at hs
    nlinarith [sq_nonneg (exteriorTaper N R x *
      fderiv ℝ (boundedExpWeight N a L) x (coordinateVector k) +
        fderiv ℝ (scaledCutoff N R) x (coordinateVector k) * boundedExpWeight N a L x)]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun k _ => hpoint k)
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,Finset.card_univ,
    nsmul_eq_mul] at hs
  have hw := mul_le_mul_of_nonneg_left (boundedExpWeight_gradient_sq_le ha hL x)
    (sq_nonneg (exteriorTaper N R x))
  unfold exteriorWeightError
  simp only [exteriorExpWeight] at hs ⊢
  nlinarith

#print axioms exteriorExpWeight_gradient_bound
end TheoremT.Continuum
