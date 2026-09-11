import PartialFourierYLaplacian_v1
import PartialFourierTLaplacian_v1
import GrushinWeightedSpectator_v1

noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators FourierTransform RealInnerProductSpace
namespace TheoremT.Continuum
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem partialFourier_weightedT (c : ℝ) {G : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → ℂ}
    (hG : ContDiff ℝ ∞ G) (hc : HasCompactSupport G) (ξ : EuclideanSpace ℝ κ) (y : EuclideanSpace ℝ ι) :
    partialFourier (grushinWeightedT c G) ξ y =
      -(c*(2*Real.pi)^2*‖ξ‖^2*‖y‖^2) • partialFourier G ξ y := by
  have he : grushinWeightedT c G = (fun p => ((c*‖p.1‖^2 : ℝ) : ℂ)*grushinTLaplacian G p) := by
    funext p; simp only [grushinWeightedT,Complex.real_smul]
  rw [he,partialFourier_y_mul (fun y : EuclideanSpace ℝ ι => ((c*‖y‖^2 : ℝ) : ℂ))
    (grushinTLaplacian G) ξ y,partialFourier_tLaplacian hG hc]
  simp only [Complex.real_smul,Complex.ofReal_neg,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_ofNat]
  ring

theorem grushin_fourier_parameter_sq {c : ℝ} (hc : 0 ≤ c) (ξ : EuclideanSpace ℝ κ) :
    (2*Real.pi*Real.sqrt c*‖ξ‖)^2 = c*(2*Real.pi)^2*‖ξ‖^2 := by
  rw [mul_pow,mul_pow,Real.sq_sqrt hc]
  ring

theorem partialFourier_grushin {c : ℝ} (hcn : 0 ≤ c)
    {G : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → ℂ}
    (hG : ContDiff ℝ ∞ G) (hc : HasCompactSupport G) (ξ : EuclideanSpace ℝ κ) (y : EuclideanSpace ℝ ι) :
    partialFourier (euclideanGrushin c G) ξ y =
      euclideanOscillator (2*Real.pi*Real.sqrt c*‖ξ‖) (partialFourier G ξ) y := by
  have he : euclideanGrushin c G = (fun p => -grushinYLaplacian G p + -(grushinWeightedT c G p)) := by
    funext p; rfl
  rw [he,partialFourier_add (G := fun p => -grushinYLaplacian G p)
    (H := fun p => -grushinWeightedT c G p) (grushinYLaplacian_contDiff hG).continuous.neg
    (grushinYLaplacian_hasCompactSupport hc).neg (grushinWeightedT_contDiff c hG).continuous.neg
    (grushinWeightedT_hasCompactSupport c hc).neg]
  rw [partialFourier_neg,partialFourier_neg,partialFourier_yLaplacian hG hc,partialFourier_weightedT c hG hc]
  simp only [euclideanOscillator,oscillatorLaplacian,grushin_fourier_parameter_sq hcn,neg_smul,neg_neg]

#print axioms partialFourier_weightedT
#print axioms grushin_fourier_parameter_sq
#print axioms partialFourier_grushin
end TheoremT.Continuum
