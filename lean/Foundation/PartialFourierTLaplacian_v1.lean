import EuclideanGrushinPrincipal_v1
import PartialFourierSpectatorDerivative_v1
import PartialFourierLinear_v1

noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators FourierTransform RealInnerProductSpace
namespace TheoremT.Continuum
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem euclidean_inner_oscillatorBasis (ξ : EuclideanSpace ℝ κ) (k : κ) :
    ⟪ξ,oscillatorBasis k⟫ = ξ k := by
  simp [oscillatorBasis,EuclideanSpace.inner_single_right]

theorem partialFourier_tLaplacian {G : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → ℂ}
    (hG : ContDiff ℝ ∞ G) (hc : HasCompactSupport G) (ξ : EuclideanSpace ℝ κ) (y : EuclideanSpace ℝ ι) :
    partialFourier (grushinTLaplacian G) ξ y =
      -((2*Real.pi)^2*‖ξ‖^2) • partialFourier G ξ y := by
  unfold grushinTLaplacian
  rw [partialFourier_finset_sum]
  · simp_rw [partialFourier_second_tDirectional hG hc,euclidean_inner_oscillatorBasis]
    rw [EuclideanSpace.real_norm_sq_eq,Finset.mul_sum,← Finset.sum_neg_distrib,Finset.sum_smul]
  · intro k _
    exact (partialTDirectional_contDiff (partialTDirectional_contDiff hG _) _).continuous
  · intro k _
    exact partialTDirectional_hasCompactSupport (partialTDirectional_hasCompactSupport hc _) _

#print axioms euclidean_inner_oscillatorBasis
#print axioms partialFourier_tLaplacian
end TheoremT.Continuum
