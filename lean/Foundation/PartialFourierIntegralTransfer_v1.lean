import PartialFourierPlancherelProduct_v1

noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators
namespace TheoremT.Continuum
variable {Y T : Type} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T]
  [MeasurableSpace T] [BorelSpace T] [FiniteDimensional ℝ T]

theorem partialFourier_fiber_norm_sq_integrable {G : Y × T → ℂ} (hG : ContDiff ℝ ∞ G)
    (hc : HasCompactSupport G) : Integrable (fun ξ => ∫ y,‖partialFourier G ξ y‖^2) volume :=
  (partialFourier_joint_norm_sq_integrable hG hc).integral_prod_right

theorem partialFourier_integrated_sum_le {α : Type*} (s : Finset α) (a : α → ℝ) (b : ℝ)
    (G : α → Y × T → ℂ) {H : Y × T → ℂ}
    (hG : ∀ i ∈ s, ContDiff ℝ ∞ (G i)) (hcG : ∀ i ∈ s, HasCompactSupport (G i))
    (hH : ContDiff ℝ ∞ H) (hcH : HasCompactSupport H)
    (h : ∀ ξ, (∑ i ∈ s, a i * (∫ y,‖partialFourier (G i) ξ y‖^2)) ≤
      b * (∫ y,‖partialFourier H ξ y‖^2)) :
    (∑ i ∈ s, a i * (∫ p,‖G i p‖^2 ∂((volume : Measure Y).prod (volume : Measure T)))) ≤
      b * (∫ p,‖H p‖^2 ∂((volume : Measure Y).prod (volume : Measure T))) := by
  have hI (i : α) (hi : i ∈ s) :=
    (partialFourier_fiber_norm_sq_integrable (hG i hi) (hcG i hi)).const_mul (a i)
  have hB := (partialFourier_fiber_norm_sq_integrable hH hcH).const_mul b
  have hh := integral_mono (integrable_finsetSum s hI) hB h
  rw [integral_finsetSum _ hI,integral_const_mul] at hh
  simp_rw [integral_const_mul] at hh
  rw [partialFourier_plancherel_product hH hcH] at hh
  have he : (∑ i ∈ s, a i * (∫ ξ,∫ y,‖partialFourier (G i) ξ y‖^2)) =
      ∑ i ∈ s, a i * (∫ p,‖G i p‖^2 ∂((volume : Measure Y).prod (volume : Measure T))) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [partialFourier_plancherel_product (hG i hi) (hcG i hi)]
  rwa [he] at hh

#print axioms partialFourier_fiber_norm_sq_integrable
#print axioms partialFourier_integrated_sum_le
end TheoremT.Continuum
