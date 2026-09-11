import HardyLimitComplex_v1
import Mathlib.MeasureTheory.Group.Integral

/-! Translation of the verified compact complex three-dimensional Hardy bound.
The singularity may be at any fixed point; the constant remains exactly four. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace TheoremT.Hardy

theorem shifted_complex_hardy_integrable_sq_and_bound {u : R3 → ℂ}
    (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u) (a : R3) :
    Integrable (fun x => ‖u x‖^2 / ‖x - a‖^2) volume ∧
      (∫ x, ‖u x‖^2 / ‖x - a‖^2) ≤
        4 * (∫ x, ∑ k : Fin 3, ‖fderiv ℝ u x (basisVector k)‖^2) := by
  have ht : ContDiff ℝ 1 (fun y => u (y + a)) :=
    hu.comp (contDiff_id.add contDiff_const)
  have hct : HasCompactSupport (fun y => u (y + a)) :=
    huc.comp_homeomorph (Homeomorph.addRight a)
  have h := complex_hardy_integrable_sq_and_bound ht hct
  have hmp := measurePreserving_add_right (volume : Measure R3) a
  have hemb := (Homeomorph.addRight a).measurableEmbedding
  have hint : Integrable (fun x => ‖u x‖^2 / ‖x - a‖^2) volume := by
    apply (hmp.integrable_comp_emb hemb).mp
    simpa only [Function.comp_def, add_sub_cancel_right] using h.1
  refine ⟨hint, ?_⟩
  have hw := integral_add_right_eq_self (μ := (volume : Measure R3))
    (fun x : R3 => ‖u x‖^2 / ‖x - a‖^2) a
  simp only [add_sub_cancel_right] at hw
  have he := integral_add_right_eq_self (μ := (volume : Measure R3))
    (fun x : R3 => ∑ k : Fin 3, ‖fderiv ℝ u x (basisVector k)‖^2) a
  simpa only [fderiv_comp_add_right, add_sub_cancel_right, hw, he] using h.2

#print axioms shifted_complex_hardy_integrable_sq_and_bound
end TheoremT.Hardy
