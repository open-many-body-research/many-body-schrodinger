import ManyBody.S2.Internal.CylindricalCoulombReduction
import ManyBody.S2.Internal.CoulombWedgeIntegration
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection


/-! Newton radial convolution in canonical Euclidean volume. The shell kernel follows from the proved height integral and justified Fubini bridge. An actual volume-preserving reflection aligns any nonzero center; original integral integrability remains an explicit analytic premise. -/

noncomputable section
open MeasureTheory Set
namespace ManyBody.S2.Internal.Cylindrical
open CoulombAngular

theorem integral_radial_coulomb_axis (s : ℝ) (hs : 0 < s) {f : ℝ → ℝ}
    (hfm : Measurable f) (hf : ∀ r, 0 ≤ f r)
    (hfi : IntegrableOn (fun r : ℝ => r^2*f r) (Ioi 0))
    (hactual : Integrable (fun x : Space => f ‖x‖ / ‖x-axisPoint s‖)) :
    (∫ x : Space, f ‖x‖ / ‖x-axisPoint s‖) =
      (4*Real.pi) * ∫ r : ℝ in Ioi 0, r^2*f r / max r s := by
  rw [integral_radial_coulomb_cylindrical s f hactual]
  have he : (fun z : ℝ => ∫ r : ℝ in Ioi |z|,
      r*f r / Real.sqrt (r^2-2*s*z+s^2)) =
      (fun z : ℝ => ∫ r : ℝ in Ioi |z|,
      r*f r / Real.sqrt (r^2+s^2-2*s*z)) := by
    funext z
    apply integral_congr_ae
    filter_upwards [] with r
    congr 2
    ring
  rw [he,integral_wedge s hs hfm hf hfi]
  ring

theorem axisPoint_norm (s : ℝ) : ‖axisPoint s‖ = |s| := by
  have h := assemble_norm_sq (axisReal.symm s) 0
  change ‖axisPoint s‖^2 = ‖axisReal.symm s‖^2+‖(0 : Plane)‖^2 at h
  rw [axisReal.symm.norm_map,Real.norm_eq_abs,norm_zero,zero_pow (by norm_num : (2 : ℕ) ≠ 0),add_zero] at h
  nlinarith [norm_nonneg (axisPoint s),abs_nonneg s]

/-- Newton's radial convolution formula in actual canonical three-dimensional volume. -/
theorem integral_radial_coulomb (y : Space) (hy : 0 < ‖y‖) {f : ℝ → ℝ}
    (hfm : Measurable f) (hf : ∀ r, 0 ≤ f r)
    (hfi : IntegrableOn (fun r : ℝ => r^2*f r) (Ioi 0))
    (hactual : Integrable (fun x : Space => f ‖x‖ / ‖x-y‖)) :
    (∫ x : Space, f ‖x‖ / ‖x-y‖) =
      (4*Real.pi) * ∫ r : ℝ in Ioi 0, r^2*f r / max r ‖y‖ := by
  let R := Submodule.reflection (ℝ ∙ (y-axisPoint ‖y‖))ᗮ
  have hR : R y = axisPoint ‖y‖ := by
    apply Submodule.reflection_sub
    rw [axisPoint_norm,abs_of_nonneg (norm_nonneg y)]
  have hRi : R.symm (axisPoint ‖y‖) = y := by
    rw [← hR,R.symm_apply_apply]
  have haxis : Integrable (fun x : Space => f ‖x‖ / ‖x-axisPoint ‖y‖‖) := by
    have ht := R.symm.measurePreserving.integrable_comp_of_integrable hactual
    apply ht.congr
    filter_upwards [] with x
    simp only [Function.comp_apply,R.symm.norm_map]
    have hd : R.symm x-y = R.symm (x-axisPoint ‖y‖) := by rw [map_sub,hRi]
    rw [hd,R.symm.norm_map]
  have ht := R.measurePreserving.integral_comp R.toHomeomorph.measurableEmbedding
    (fun x : Space => f ‖x‖ / ‖x-axisPoint ‖y‖‖)
  have ht' : (∫ x : Space, f ‖x‖ / ‖x-y‖) =
      ∫ x : Space, f ‖x‖ / ‖x-axisPoint ‖y‖‖ := by
    convert ht using 1
    apply integral_congr_ae
    filter_upwards [] with x
    rw [R.norm_map,← hR,← map_sub,R.norm_map]
  rw [ht',integral_radial_coulomb_axis ‖y‖ hy hfm hf hfi haxis]

#print axioms integral_radial_coulomb
end ManyBody.S2.Internal.Cylindrical