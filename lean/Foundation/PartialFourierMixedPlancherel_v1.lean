import PartialFourierPlancherelProduct_v1

noncomputable section
open MeasureTheory
open scoped ContDiff FourierTransform SchwartzMap
namespace TheoremT.Continuum
variable {Y T : Type} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T]
  [MeasurableSpace T] [BorelSpace T] [FiniteDimensional ℝ T]

theorem partialFourier_slice_plancherel_mixed {G : Y × T → ℂ}
    (hc : HasCompactSupport G) (hs : ∀ y, ContDiff ℝ ∞ (fun t => G (y,t))) (y : Y) :
    Integrable (fun ξ => ‖partialFourier G ξ y‖^2) volume ∧
      (∫ ξ,‖partialFourier G ξ y‖^2) = ∫ t,‖G (y,t)‖^2 := by
  let f : 𝓢(T,ℂ) := (compact_slice_hasCompactSupport hc y).toSchwartzMap (hs y)
  exact ⟨((𝓕 f).memLp 2 volume).integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0),
    SchwartzMap.integral_norm_sq_fourier f⟩

theorem partialFourier_joint_norm_sq_integrable_mixed {G : Y × T → ℂ}
    (hG : Continuous G) (hc : HasCompactSupport G) (hs : ∀ y, ContDiff ℝ ∞ (fun t => G (y,t))) :
    Integrable (fun p : Y × T => ‖partialFourier G p.2 p.1‖^2)
      ((volume : Measure Y).prod (volume : Measure T)) := by
  have hm := (partialFourier_joint_stronglyMeasurable hG).norm.pow 2
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall (fun y => (partialFourier_slice_plancherel_mixed hc hs y).1),?_⟩
  change Integrable (fun y : Y => ∫ ξ,‖‖partialFourier G ξ y‖^2‖) volume
  have he (y : Y) : (∫ ξ,‖‖partialFourier G ξ y‖^2‖) = ∫ t,‖G (y,t)‖^2 := by
    simpa only [norm_pow,norm_norm] using (partialFourier_slice_plancherel_mixed hc hs y).2
  simpa only [he] using (compact_joint_norm_sq_integrable hG hc).integral_prod_left

theorem partialFourier_plancherel_product_mixed {G : Y × T → ℂ}
    (hG : Continuous G) (hc : HasCompactSupport G) (hs : ∀ y, ContDiff ℝ ∞ (fun t => G (y,t))) :
    (∫ ξ, ∫ y,‖partialFourier G ξ y‖^2) =
      ∫ p,‖G p‖^2 ∂((volume : Measure Y).prod (volume : Measure T)) := by
  rw [← integral_integral_swap (partialFourier_joint_norm_sq_integrable_mixed hG hc hs)]
  simp_rw [(partialFourier_slice_plancherel_mixed hc hs _).2]
  exact (integral_prod _ (compact_joint_norm_sq_integrable hG hc)).symm

#print axioms partialFourier_slice_plancherel_mixed
#print axioms partialFourier_joint_norm_sq_integrable_mixed
#print axioms partialFourier_plancherel_product_mixed
end TheoremT.Continuum
