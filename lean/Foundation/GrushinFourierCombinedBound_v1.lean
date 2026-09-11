import EuclideanOscillatorCombinedBound_v1
import GrushinFourierMixedBound_v1

noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators FourierTransform
namespace TheoremT.Continuum
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem partialFourier_mixed_weighted_integral
    {G : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ κ → ℂ}
    (hG : ContDiff ℝ ∞ G) (hc : HasCompactSupport G) (ξ : EuclideanSpace ℝ κ) :
    (∑ i : Fin 4,∑ j : κ,∫ y,‖y‖^2 *
      ‖partialFourier (partialTDirectional (partialYDirectional G (oscillatorBasis i)) (oscillatorBasis j)) ξ y‖^2) =
    (2*Real.pi)^2*‖ξ‖^2*(∫ y,‖y‖^2*(∑ i : Fin 4,‖oscillatorPartial (partialFourier G ξ) i y‖^2)) := by
  have hI (i : Fin 4) (j : κ) := partialFourier_weighted_slice_integrable continuous_norm
    (partialTDirectional_contDiff (partialYDirectional_contDiff hG (oscillatorBasis i)) (oscillatorBasis j))
    (partialTDirectional_hasCompactSupport (partialYDirectional_hasCompactSupport hc (oscillatorBasis i)) (oscillatorBasis j)) ξ
  have hrow (i : Fin 4) :
      (∑ j : κ,∫ y,‖y‖^2 *
        ‖partialFourier (partialTDirectional (partialYDirectional G (oscillatorBasis i)) (oscillatorBasis j)) ξ y‖^2) =
      ∫ y,∑ j : κ,‖y‖^2 *
        ‖partialFourier (partialTDirectional (partialYDirectional G (oscillatorBasis i)) (oscillatorBasis j)) ξ y‖^2 :=
    (integral_finsetSum _ (fun j _ => hI i j)).symm
  simp_rw [hrow]
  rw [← integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hI i j))]
  simp_rw [partialFourier_mixed_weighted_sum hG hc]
  rw [integral_const_mul]

theorem grushin_fourier_combined_bound {c : ℝ} (hcn : 0 ≤ c)
    {G : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ κ → ℂ}
    (hG : ContDiff ℝ ∞ G) (hc : HasCompactSupport G) (ξ : EuclideanSpace ℝ κ) :
    (∫ y,‖partialFourier (grushinYLaplacian G) ξ y‖^2) +
      (∫ y,‖partialFourier (grushinWeightedT c G) ξ y‖^2) +
      2*c*(∑ i : Fin 4,∑ j : κ,∫ y,‖y‖^2 *
        ‖partialFourier (partialTDirectional (partialYDirectional G (oscillatorBasis i)) (oscillatorBasis j)) ξ y‖^2) ≤
      (3/2 : ℝ)*(∫ y,‖partialFourier (euclideanGrushin c G) ξ y‖^2) := by
  have hh := compact_four_dimensional_oscillator_combined_bound
    (partialFourier_contDiff hG hc ξ) (partialFourier_hasCompactSupport hc ξ)
    (a := 2*Real.pi*Real.sqrt c*‖ξ‖) (by positivity)
  rw [grushin_fourier_parameter_sq hcn ξ] at hh
  simp_rw [partialFourier_yLaplacian hG hc,
    partialFourier_weightedT_norm_sq hcn hG hc,partialFourier_grushin hcn hG hc]
  rw [integral_const_mul,partialFourier_mixed_weighted_integral hG hc]
  nlinarith only [hh]

#print axioms partialFourier_mixed_weighted_integral
#print axioms grushin_fourier_combined_bound
end TheoremT.Continuum
