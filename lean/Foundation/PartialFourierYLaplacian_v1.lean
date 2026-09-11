import EuclideanGrushinPrincipal_v1
import CompactPartialFourierYDerivative_v1
import PartialFourierLinear_v1

noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators FourierTransform
namespace TheoremT.Continuum
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem partialFourier_oscillatorPartial {G : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → ℂ}
    (hG : ContDiff ℝ ∞ G) (hc : HasCompactSupport G) (ξ : EuclideanSpace ℝ κ) (k : ι) :
    oscillatorPartial (partialFourier G ξ) k =
      partialFourier (partialYDirectional G (oscillatorBasis k)) ξ := by
  funext y
  exact partialFourier_yDirectional hG hc ξ y (oscillatorBasis k)

theorem partialFourier_yLaplacian {G : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → ℂ}
    (hG : ContDiff ℝ ∞ G) (hc : HasCompactSupport G) (ξ : EuclideanSpace ℝ κ) (y : EuclideanSpace ℝ ι) :
    partialFourier (grushinYLaplacian G) ξ y = oscillatorLaplacian (partialFourier G ξ) y := by
  unfold grushinYLaplacian
  rw [partialFourier_finset_sum]
  · unfold oscillatorLaplacian
    apply Finset.sum_congr rfl
    intro k _
    rw [partialFourier_oscillatorPartial hG hc ξ k]
    exact (partialFourier_yDirectional (partialYDirectional_contDiff hG _)
      (partialYDirectional_hasCompactSupport hc _) ξ y (oscillatorBasis k)).symm
  · intro k _
    exact (partialYDirectional_contDiff (partialYDirectional_contDiff hG _) _).continuous
  · intro k _
    exact partialYDirectional_hasCompactSupport (partialYDirectional_hasCompactSupport hc _) _

#print axioms partialFourier_oscillatorPartial
#print axioms partialFourier_yLaplacian
end TheoremT.Continuum
