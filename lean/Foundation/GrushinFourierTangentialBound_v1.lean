import PartialFourierGrushin_v1
import PartialFourierGradientSquare_v1
import EuclideanOscillatorNorm_v1
import PartialFourierPlancherelProduct_v1

noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators FourierTransform
namespace TheoremT.Continuum
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem grushin_fourier_tangential_bound {c : ℝ} (hcn : 0 ≤ c)
    {G : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ κ → ℂ}
    (hG : ContDiff ℝ ∞ G) (hc : HasCompactSupport G) (ξ : EuclideanSpace ℝ κ) :
    (∑ k : κ, (16*c) * (∫ y,‖partialFourier (partialTDirectional G (oscillatorBasis k)) ξ y‖^2)) ≤
      ∫ y,‖partialFourier (euclideanGrushin c G) ξ y‖^2 := by
  have hI (k : κ) : Integrable
      (fun y => ‖partialFourier (partialTDirectional G (oscillatorBasis k)) ξ y‖^2) volume := by
    have hD := partialTDirectional_contDiff hG (oscillatorBasis k)
    have hcD := partialTDirectional_hasCompactSupport hc (oscillatorBasis k)
    have hh := (partialFourier_contDiff hD hcD ξ).continuous
    have hhc := partialFourier_hasCompactSupport hcD ξ
    apply (hh.norm.pow 2).integrable_of_hasCompactSupport
    simpa only [sq] using hhc.norm.mul_right (f' := fun y => ‖partialFourier (partialTDirectional G (oscillatorBasis k)) ξ y‖)
  rw [← Finset.mul_sum,← integral_finsetSum _ (fun k _ => hI k)]
  simp_rw [partialFourier_tGradient_norm_sq hG hc]
  rw [integral_const_mul]
  have hh := compact_euclidean_oscillator_integral_lower
    (partialFourier_contDiff hG hc ξ) (partialFourier_hasCompactSupport hc ξ)
    (a := 2*Real.pi*Real.sqrt c*‖ξ‖) (by positivity)
  simp only [Fintype.card_fin,Nat.cast_ofNat,mul_pow] at hh
  rw [Real.sq_sqrt hcn] at hh
  have he (y : EuclideanSpace ℝ (Fin 4)) := partialFourier_grushin hcn hG hc ξ y
  simp_rw [he]
  nlinarith only [hh]

#print axioms grushin_fourier_tangential_bound
end TheoremT.Continuum
