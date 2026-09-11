import PartialFourierWeightedPlancherel_v1
import PartialFourierIntegralTransfer_v1

noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators
namespace TheoremT.Continuum
variable {Y T : Type} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T]
  [MeasurableSpace T] [BorelSpace T] [FiniteDimensional ℝ T]

theorem partialFourier_weighted_slice_integrable {w : Y → ℝ} (hw : Continuous w)
    {G : Y × T → ℂ} (hG : ContDiff ℝ ∞ G) (hc : HasCompactSupport G) (ξ : T) :
    Integrable (fun y => (w y)^2*‖partialFourier G ξ y‖^2) volume := by
  have hF := (partialFourier_contDiff hG hc ξ).continuous
  have hcF := partialFourier_hasCompactSupport hc ξ
  have hs : HasCompactSupport (fun y => ‖partialFourier G ξ y‖^2) := by
    apply hcF.mono
    intro y hy
    change partialFourier G ξ y ≠ 0
    intro hz
    exact hy (by simp [hz])
  exact ((hw.pow 2).mul (hF.norm.pow 2)).integrable_of_hasCompactSupport hs.mul_left

theorem partialFourier_weighted_integrated_sum_le {w : Y → ℝ} (hw : Continuous w)
    {α : Type*} (s : Finset α) (a : α → ℝ) (b : ℝ) (G : α → Y × T → ℂ) {H : Y × T → ℂ}
    (hG : ∀ i ∈ s, ContDiff ℝ ∞ (G i)) (hcG : ∀ i ∈ s, HasCompactSupport (G i))
    (hH : ContDiff ℝ ∞ H) (hcH : HasCompactSupport H)
    (h : ∀ ξ, (∑ i ∈ s, a i * (∫ y,(w y)^2*‖partialFourier (G i) ξ y‖^2)) ≤
      b * (∫ y,‖partialFourier H ξ y‖^2)) :
    (∑ i ∈ s, a i * (∫ p,(w p.1)^2*‖G i p‖^2 ∂((volume : Measure Y).prod (volume : Measure T)))) ≤
      b * (∫ p,‖H p‖^2 ∂((volume : Measure Y).prod (volume : Measure T))) := by
  have hI (i : α) (hi : i ∈ s) :=
    (partialFourier_weighted_plancherel hw (hG i hi) (hcG i hi)).1.const_mul (a i)
  have hB := (partialFourier_fiber_norm_sq_integrable hH hcH).const_mul b
  have hh := integral_mono (integrable_finsetSum s hI) hB h
  rw [integral_finsetSum _ hI,integral_const_mul] at hh
  simp_rw [integral_const_mul] at hh
  rw [partialFourier_plancherel_product hH hcH] at hh
  have he : (∑ i ∈ s, a i * (∫ ξ,∫ y,(w y)^2*‖partialFourier (G i) ξ y‖^2)) =
      ∑ i ∈ s, a i * (∫ p,(w p.1)^2*‖G i p‖^2 ∂((volume : Measure Y).prod (volume : Measure T))) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [(partialFourier_weighted_plancherel hw (hG i hi) (hcG i hi)).2]
  rwa [he] at hh

#print axioms partialFourier_weighted_slice_integrable
#print axioms partialFourier_weighted_integrated_sum_le
end TheoremT.Continuum
