import NewtonSmoothRepresentation_v1
import NewtonWeakGradient_v1
import SmoothTestLaplacian_v1
import Mathlib.Analysis.Calculus.ContDiff.Convolution

noncomputable section
open MeasureTheory
open scoped ContDiff Convolution
namespace TheoremT.Continuum

theorem smooth_compact_newton_gradient_representation {N : ℕ} (hN : 0 < N)
    {φ : Configuration N → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (x : Configuration N) (k : Coordinate N) :
    (∫ y, normalizedNewtonGradient N k y*realTestLaplacian φ (x-y))=
      fderiv ℝ φ x (coordinateVector k) := by
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.mul ℝ ℝ
  have hL := realTestLaplacian_contDiff hφ
  have hcL := realTestLaplacian_compact hc
  have hΓ := normalizedNewtonPotential_locallyIntegrable hN
  have hEq : (normalizedNewtonPotential N ⋆[L,volume] realTestLaplacian φ)=φ := by
    funext z
    exact smooth_compact_newton_representation hN hφ hc z
  have hd := hcL.hasFDerivAt_convolution_right L hΓ (hL.of_le (by norm_num)) x
  rw [hEq] at hd
  have hder : fderiv ℝ φ x (coordinateVector k) =
      ∫ y, normalizedNewtonPotential N y*fderiv ℝ (realTestLaplacian φ) (x-y) (coordinateVector k) := by
    rw [hd.fderiv,convolution_def,ContinuousLinearMap.integral_apply]
    · rfl
    · exact (hcL.fderiv ℝ).convolutionExists_right (L.precompR (Configuration N)) hΓ
        (hL.continuous_fderiv (by simp)) x
  have ht : ContDiff ℝ ∞ (fun y => realTestLaplacian φ (x-y)) := hL.comp (contDiff_const.sub contDiff_id)
  have hct : HasCompactSupport (fun y => realTestLaplacian φ (x-y)) :=
    hcL.comp_homeomorph (Homeomorph.subLeft x)
  have hh := normalizedNewtonPotential_weak_partial_test hN k ht hct
  simp_rw [reflected_real_test_partial hL,neg_mul,integral_neg,neg_neg] at hh
  rw [hder]
  simpa only [mul_comm] using hh

#print axioms smooth_compact_newton_gradient_representation
end TheoremT.Continuum
