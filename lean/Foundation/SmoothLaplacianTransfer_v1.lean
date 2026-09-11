import LocalWeakLaplacian_v1
import ConfigurationSmoothGreen_v1

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace TheoremT.Continuum

theorem configuration_integral_laplacian_transfer {N : ℕ} {φ f : Configuration N → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport φ) :
    (∫ x, φ x*realTestLaplacian f x) = ∫ x, realTestLaplacian φ x*f x := by
  have hD (u : Configuration N → ℝ) (hu : ContDiff ℝ ∞ u) (k : Coordinate N) :
      Continuous (fun x => fderiv ℝ (fun y => fderiv ℝ u y (coordinateVector k)) x (coordinateVector k)) := by
    have hd : ContDiff ℝ ∞ (fun y => fderiv ℝ u y (coordinateVector k)) :=
      (hu.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
    exact (hd.continuous_fderiv (by simp)).clm_apply continuous_const
  have hi (k : Coordinate N) : Integrable (fun x => φ x*fderiv ℝ
      (fun y => fderiv ℝ f y (coordinateVector k)) x (coordinateVector k)) volume :=
    (hφ.continuous.mul (hD f hf k)).integrable_of_hasCompactSupport hc.mul_right
  have hj (k : Coordinate N) : Integrable (fun x => fderiv ℝ
      (fun y => fderiv ℝ φ y (coordinateVector k)) x (coordinateVector k)*f x) volume :=
    ((hD φ hφ k).mul hf.continuous).integrable_of_hasCompactSupport
      ((hc.fderiv_apply ℝ (coordinateVector k)).fderiv_apply ℝ (coordinateVector k)).mul_right
  simp only [realTestLaplacian,Finset.mul_sum,Finset.sum_mul]
  rw [integral_finset_sum _ (fun k _ => hi k),integral_finset_sum _ (fun k _ => hj k)]
  apply Finset.sum_congr rfl
  intro k hk
  exact configuration_integral_mixed_transfer hφ hf hc (coordinateVector k) (coordinateVector k)

#print axioms configuration_integral_laplacian_transfer
end TheoremT.Continuum
