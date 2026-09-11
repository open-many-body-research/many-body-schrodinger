import NewtonSmoothGradientRepresentation_v1
import SmoothComplexLaplacianProjection_v1
import NormalizedNewtonGradientLp_v1

noncomputable section
open MeasureTheory
open scoped ContDiff Convolution
namespace TheoremT.Continuum

theorem smooth_compact_complex_newton_gradient_representation {N : ℕ} (hN : 0 < N)
    {φ : Configuration N → ℂ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (x : Configuration N) (k : Coordinate N) :
    (∫ y, normalizedNewtonGradient N k y • smoothLaplacian φ (x-y))=smoothPartial φ k x := by
  let M : ℝ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.lsmul ℝ ℝ
  have hi : Integrable (fun y => normalizedNewtonGradient N k y • smoothLaplacian φ (x-y)) :=
    (smoothLaplacian_compact hc).convolutionExists_right M
      (normalizedNewtonGradient_locallyIntegrable hN k) (smoothLaplacian_contDiff hφ).continuous x
  have he (L : ℂ →L[ℝ] ℝ) :
      L (∫ y, normalizedNewtonGradient N k y • smoothLaplacian φ (x-y))=L (smoothPartial φ k x) := by
    have hL : ContDiff ℝ ∞ (fun y => L (φ y)) := L.contDiff.comp hφ
    have hcL : HasCompactSupport (fun y => L (φ y)) := hc.comp_left (map_zero L)
    calc
      _ = ∫ y, L (normalizedNewtonGradient N k y • smoothLaplacian φ (x-y)) :=
        (L.integral_comp_comm hi).symm
      _ = ∫ y, normalizedNewtonGradient N k y * realTestLaplacian (fun z => L (φ z)) (x-y) := by
        apply integral_congr_ae
        filter_upwards with y
        rw [map_smul, smoothLaplacian_real_projection L hφ]
        rfl
      _ = fderiv ℝ (fun y => L (φ y)) x (coordinateVector k) :=
        smooth_compact_newton_gradient_representation hN hL hcL x k
      _ = _ := smoothPartial_real_projection L hφ x k
  apply Complex.ext
  · exact he Complex.reCLM
  · exact he Complex.imCLM

#print axioms smooth_compact_complex_newton_gradient_representation
end TheoremT.Continuum
