import PartialFourierMeasurable_v1
import CompactPartialFourierPlancherelSlice_v1

noncomputable section
open MeasureTheory
open scoped ContDiff FourierTransform
namespace TheoremT.Continuum
variable {Y T : Type} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T]
  [MeasurableSpace T] [BorelSpace T] [FiniteDimensional ℝ T]

theorem compact_joint_norm_sq_integrable {G : Y × T → ℂ} (hG : Continuous G)
    (hc : HasCompactSupport G) :
    Integrable (fun p => ‖G p‖^2) ((volume : Measure Y).prod (volume : Measure T)) := by
  apply (hG.norm.pow 2).integrable_of_hasCompactSupport
  simpa only [sq] using hc.norm.mul_right (f' := fun p => ‖G p‖)

theorem partialFourier_joint_norm_sq_integrable {G : Y × T → ℂ} (hG : ContDiff ℝ ∞ G)
    (hc : HasCompactSupport G) :
    Integrable (fun p : Y × T => ‖partialFourier G p.2 p.1‖^2)
      ((volume : Measure Y).prod (volume : Measure T)) := by
  have hm := (partialFourier_joint_stronglyMeasurable hG.continuous).norm.pow 2
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall (partialFourier_slice_norm_sq_integrable hG hc),?_⟩
  change Integrable (fun y : Y => ∫ ξ,‖‖partialFourier G ξ y‖^2‖) volume
  have he (y : Y) : (∫ ξ,‖‖partialFourier G ξ y‖^2‖) = ∫ t,‖G (y,t)‖^2 := by
    simpa only [norm_pow,norm_norm] using partialFourier_slice_plancherel hG hc y
  simpa only [he] using (compact_joint_norm_sq_integrable hG.continuous hc).integral_prod_left

theorem partialFourier_plancherel_product {G : Y × T → ℂ} (hG : ContDiff ℝ ∞ G)
    (hc : HasCompactSupport G) :
    (∫ ξ, ∫ y, ‖partialFourier G ξ y‖^2) =
      ∫ p, ‖G p‖^2 ∂((volume : Measure Y).prod (volume : Measure T)) := by
  rw [← integral_integral_swap (partialFourier_joint_norm_sq_integrable hG hc)]
  simp_rw [partialFourier_slice_plancherel hG hc]
  exact (integral_prod _ (compact_joint_norm_sq_integrable hG.continuous hc)).symm

#print axioms compact_joint_norm_sq_integrable
#print axioms partialFourier_joint_norm_sq_integrable
#print axioms partialFourier_plancherel_product
end TheoremT.Continuum
