import PartialFourierGrushin_v1
import EuclideanOscillatorComponentBounds_v1

noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators FourierTransform
namespace TheoremT.Continuum
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem partialFourier_weightedT_norm_sq {c : ℝ} (hcn : 0 ≤ c)
    {G : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ κ → ℂ}
    (hG : ContDiff ℝ ∞ G) (hc : HasCompactSupport G) (ξ : EuclideanSpace ℝ κ) (y : EuclideanSpace ℝ (Fin 4)) :
    ‖partialFourier (grushinWeightedT c G) ξ y‖^2 =
      (2*Real.pi*Real.sqrt c*‖ξ‖)^4 * (‖y‖^4*‖partialFourier G ξ y‖^2) := by
  rw [partialFourier_weightedT c hG hc]
  have ha := grushin_fourier_parameter_sq hcn ξ
  rw [← ha]
  simp only [norm_smul,norm_neg,Real.norm_eq_abs,mul_pow,sq_abs]
  ring

theorem grushin_fourier_component_bound {c : ℝ} (hcn : 0 ≤ c)
    {G : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ κ → ℂ}
    (hG : ContDiff ℝ ∞ G) (hc : HasCompactSupport G) (ξ : EuclideanSpace ℝ κ) :
    (∫ y,‖partialFourier (grushinYLaplacian G) ξ y‖^2) +
      (∫ y,‖partialFourier (grushinWeightedT c G) ξ y‖^2) ≤
        (3/2 : ℝ) * (∫ y,‖partialFourier (euclideanGrushin c G) ξ y‖^2) := by
  have h := (compact_four_dimensional_oscillator_component_bounds
    (partialFourier_contDiff hG hc ξ) (partialFourier_hasCompactSupport hc ξ)
    (a := 2*Real.pi*Real.sqrt c*‖ξ‖) (by positivity)).1
  simpa only [partialFourier_yLaplacian hG hc,partialFourier_weightedT_norm_sq hcn hG hc,
    integral_const_mul,partialFourier_grushin hcn hG hc] using h

#print axioms partialFourier_weightedT_norm_sq
#print axioms grushin_fourier_component_bound
end TheoremT.Continuum
