import PartialFourierTLaplacian_v1

noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators FourierTransform RealInnerProductSpace
namespace TheoremT.Continuum
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem partialFourier_tDirectional_norm_sq {G : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → ℂ}
    (hG : ContDiff ℝ ∞ G) (hc : HasCompactSupport G) (ξ : EuclideanSpace ℝ κ)
    (y : EuclideanSpace ℝ ι) (k : κ) :
    ‖partialFourier (partialTDirectional G (oscillatorBasis k)) ξ y‖^2 =
      (2*Real.pi)^2*(ξ k)^2*‖partialFourier G ξ y‖^2 := by
  rw [partialFourier_tDirectional hG hc,euclidean_inner_oscillatorBasis]
  have he : (2*Real.pi*Complex.I : ℂ) = ((2*Real.pi : ℝ) : ℂ)*Complex.I := by push_cast; rfl
  rw [he]
  simp only [norm_mul,Complex.norm_real,Complex.norm_I,mul_one,mul_pow,Real.norm_eq_abs,sq_abs]

theorem partialFourier_tGradient_norm_sq {G : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → ℂ}
    (hG : ContDiff ℝ ∞ G) (hc : HasCompactSupport G) (ξ : EuclideanSpace ℝ κ)
    (y : EuclideanSpace ℝ ι) :
    (∑ k : κ,‖partialFourier (partialTDirectional G (oscillatorBasis k)) ξ y‖^2) =
      (2*Real.pi)^2*‖ξ‖^2*‖partialFourier G ξ y‖^2 := by
  simp_rw [partialFourier_tDirectional_norm_sq hG hc]
  rw [← Finset.sum_mul,← Finset.mul_sum,← EuclideanSpace.real_norm_sq_eq]

#print axioms partialFourier_tDirectional_norm_sq
#print axioms partialFourier_tGradient_norm_sq
end TheoremT.Continuum
