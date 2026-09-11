import PartialFourierYLaplacian_v1
import PartialFourierGradientSquare_v1

noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators FourierTransform
namespace TheoremT.Continuum
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem partialFourier_mixed_weighted_sum {G : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → ℂ}
    (hG : ContDiff ℝ ∞ G) (hc : HasCompactSupport G) (ξ : EuclideanSpace ℝ κ) (y : EuclideanSpace ℝ ι) :
    (∑ i : ι,∑ j : κ, ‖y‖^2 *
      ‖partialFourier (partialTDirectional (partialYDirectional G (oscillatorBasis i)) (oscillatorBasis j)) ξ y‖^2) =
    (2*Real.pi)^2*‖ξ‖^2*(‖y‖^2*(∑ i : ι,‖oscillatorPartial (partialFourier G ξ) i y‖^2)) := by
  have hi (i : ι) :
      (∑ j : κ, ‖y‖^2 *
        ‖partialFourier (partialTDirectional (partialYDirectional G (oscillatorBasis i)) (oscillatorBasis j)) ξ y‖^2) =
      ((2*Real.pi)^2*‖ξ‖^2) * (‖y‖^2*‖oscillatorPartial (partialFourier G ξ) i y‖^2) := by
    rw [← Finset.mul_sum,partialFourier_tGradient_norm_sq (partialYDirectional_contDiff hG _)
      (partialYDirectional_hasCompactSupport hc _)]
    rw [← congrFun (partialFourier_oscillatorPartial hG hc ξ i) y]
    ring
  simp_rw [hi]
  rw [← Finset.mul_sum,← Finset.mul_sum]

#print axioms partialFourier_mixed_weighted_sum
end TheoremT.Continuum
