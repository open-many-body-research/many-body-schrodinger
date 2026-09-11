import RegularizedRadiusLaplacian_v1
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-! Integration by parts with compactness only on the test function.
The smooth coefficient may grow at infinity. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum

theorem configuration_integral_mul_fderiv_compact {N : ℕ} {u w : Configuration N → ℝ}
    (hu : ContDiff ℝ 1 u) (hw : ContDiff ℝ 1 w)
    (huc : HasCompactSupport u) (v : Configuration N) :
    (∫ x, u x*fderiv ℝ w x v) = -(∫ x, fderiv ℝ u x v*w x) := by
  have hdu : Continuous (fun x => fderiv ℝ u x v) :=
    (hu.continuous_fderiv_apply (by norm_num)).comp (continuous_id.prodMk continuous_const)
  have hdw : Continuous (fun x => fderiv ℝ w x v) :=
    (hw.continuous_fderiv_apply (by norm_num)).comp (continuous_id.prodMk continuous_const)
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact (hdu.mul hw.continuous).integrable_of_hasCompactSupport (huc.fderiv_apply ℝ v).mul_right
  · exact (hu.continuous.mul hdw).integrable_of_hasCompactSupport huc.mul_right
  · exact (hu.continuous.mul hw.continuous).integrable_of_hasCompactSupport huc.mul_right
  · intro x _; exact hu.differentiable (by norm_num) x
  · intro x _; exact hw.differentiable (by norm_num) x

theorem configuration_integral_mixed_transfer {N : ℕ} {φ f : Configuration N → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport φ)
    (v w : Configuration N) :
    (∫ x, φ x*fderiv ℝ (fun y => fderiv ℝ f y v) x w) =
      ∫ x, fderiv ℝ (fun y => fderiv ℝ φ y w) x v*f x := by
  have hdφ : ContDiff ℝ ∞ (fun y => fderiv ℝ φ y w) :=
    (hφ.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  have hdf : ContDiff ℝ ∞ (fun y => fderiv ℝ f y v) :=
    (hf.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  rw [configuration_integral_mul_fderiv_compact (hφ.of_le (by simp))
    (hdf.of_le (by simp)) hc w,
    configuration_integral_mul_fderiv_compact (hdφ.of_le (by simp))
      (hf.of_le (by simp)) (hc.fderiv_apply ℝ w) v,neg_neg]

#print axioms configuration_integral_mixed_transfer
end TheoremT.Continuum
