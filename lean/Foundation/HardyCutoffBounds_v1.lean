import HardyWeakCutoff_v2

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace TheoremT.Continuum

theorem norm_cutoffMul_le {N : ℕ} (χ : Configuration N → ℝ) (hχ : Continuous χ)
    (hcχ : HasCompactSupport χ) (f : SpatialL2 N) {A : ℝ}
    (hA : ∀ x, ‖χ x‖ ≤ A) : ‖cutoffMul χ hχ hcχ f‖ ≤ A * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [cutoffMul_ae χ hχ hcχ f] with x hx
  rw [hx, norm_smul]
  exact mul_le_mul_of_nonneg_right (hA x) (norm_nonneg _)

theorem norm_cutoff_weak_derivative_le {N : ℕ} (χ : Configuration N → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (f g : SpatialL2 N)
    (k : Coordinate N) {A B : ℝ} (hA : ∀ x, ‖χ x‖ ≤ A)
    (hB : ∀ x, ‖fderiv ℝ χ x (coordinateVector k)‖ ≤ B) :
    ‖cutoffMul χ hχ.continuous hcχ g +
      cutoffMul (fun x => fderiv ℝ χ x (coordinateVector k))
        ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const)
        (hcχ.fderiv_apply ℝ (coordinateVector k)) f‖ ≤ A * ‖g‖ + B * ‖f‖ := by
  exact (norm_add_le _ _).trans (add_le_add
    (norm_cutoffMul_le χ hχ.continuous hcχ g hA)
    (norm_cutoffMul_le _ _ _ f hB))

private theorem square_sum_bound (a b ε : ℝ) (hε : 0 < ε) :
    (a+b)^2 ≤ (1+ε)*a^2 + (1+ε⁻¹)*b^2 := by
  apply (mul_le_mul_iff_of_pos_left hε).mp
  have hs := sq_nonneg (ε*a-b)
  field_simp [hε.ne']
  nlinarith

/-- Quantitative coordinate-by-coordinate localization estimate for the exact
L² weak derivative output used in `weakPartial_cutoff`. -/
theorem cutoff_gradient_square_bound {N : ℕ} (χ : Configuration N → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (f : SpatialL2 N)
    (d : Coordinate N → SpatialL2 N) (B : Coordinate N → ℝ)
    (hχ1 : ∀ x, ‖χ x‖ ≤ 1) (hB0 : ∀ k, 0 ≤ B k)
    (hB : ∀ k x, ‖fderiv ℝ χ x (coordinateVector k)‖ ≤ B k)
    {ε : ℝ} (hε : 0 < ε) :
    (∑ k : Coordinate N, ‖cutoffMul χ hχ.continuous hcχ (d k) +
      cutoffMul (fun x => fderiv ℝ χ x (coordinateVector k))
        ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const)
        (hcχ.fderiv_apply ℝ (coordinateVector k)) f‖^2) ≤
    (1+ε) * (∑ k : Coordinate N, ‖d k‖^2) +
      (1+ε⁻¹) * (∑ k : Coordinate N, (B k)^2) * ‖f‖^2 := by
  calc
    _ ≤ ∑ k : Coordinate N, ((1+ε)*‖d k‖^2 + (1+ε⁻¹)*(B k*‖f‖)^2) := by
      apply Finset.sum_le_sum
      intro k _
      have hn := norm_cutoff_weak_derivative_le χ hχ hcχ f (d k) k hχ1 (hB k)
      simp only [one_mul] at hn
      exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans
        (square_sum_bound ‖d k‖ (B k*‖f‖) ε hε)
    _ = _ := by
      simp only [Finset.sum_add_distrib, mul_pow, ← Finset.mul_sum,
        ← Finset.sum_mul]
      ring

#print axioms norm_cutoffMul_le
#print axioms norm_cutoff_weak_derivative_le
#print axioms cutoff_gradient_square_bound
end TheoremT.Continuum
