import PolarThree_v1
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! Actual mass and nuclear-attraction polar integrals for compactly supported
complex functions. Continuity suffices; smooth test functions are a special case.
The singular nuclear term is made continuous by the actual support avoiding zero.
Sphere measure is the genuine area measure of mass 4*pi. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
set_option maxHeartbeats 1000000
namespace TheoremT.Polar

theorem compact_norm_sq_integrable {f : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hf : Continuous f) (hc : HasCompactSupport f) :
    Integrable (fun x => ‖f x‖ ^ 2) := by
  have hcont : Continuous (fun x => ‖f x‖ ^ 2) := hf.norm.pow 2
  have hcomp : HasCompactSupport (fun x => ‖f x‖ ^ 2) :=
    hc.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)
  exact hcont.integrable_of_hasCompactSupport hcomp

theorem compact_off_zero_norm_sq_div_norm_continuous
    {f : EuclideanSpace ℝ (Fin 3) → ℂ} (hf : Continuous f)
    (h0 : (0 : EuclideanSpace ℝ (Fin 3)) ∉ tsupport f) :
    Continuous (fun x => ‖f x‖ ^ 2 / ‖x‖) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst x
    apply (continuousAt_const : ContinuousAt
      (fun _ : EuclideanSpace ℝ (Fin 3) => (0 : ℝ)) 0).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds h0] with y hy
    simp [image_eq_zero_of_notMem_tsupport hy]
  · exact (hf.norm.pow 2).continuousAt.div continuous_norm.continuousAt
      (norm_ne_zero_iff.mpr hx)

theorem compact_off_zero_norm_sq_div_norm_integrable
    {f : EuclideanSpace ℝ (Fin 3) → ℂ} (hf : Continuous f)
    (hc : HasCompactSupport f) (h0 : (0 : EuclideanSpace ℝ (Fin 3)) ∉ tsupport f) :
    Integrable (fun x => ‖f x‖ ^ 2 / ‖x‖) := by
  have hdiv : HasCompactSupport (fun x => ‖f x‖ ^ 2 / ‖x‖) := by
    rw [hasCompactSupport_iff_eventuallyEq] at hc ⊢
    filter_upwards [hc] with x hx
    simp [hx]
  exact (compact_off_zero_norm_sq_div_norm_continuous hf h0).integrable_of_hasCompactSupport hdiv

theorem compact_mass_polar_radius_outer {f : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hf : Continuous f) (hc : HasCompactSupport f) :
    (∫ x : EuclideanSpace ℝ (Fin 3), ‖f x‖ ^ 2) =
      ∫ r : ℝ in Ioi 0, r ^ 2 *
        (∫ w : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
          ‖f (r • w.val)‖ ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere) := by
  simpa only [smul_eq_mul] using integral_polar_dim_three_radius_outer
    (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3)
    (fun x => ‖f x‖ ^ 2) (compact_norm_sq_integrable hf hc)

theorem compact_mass_polar_sphere_outer {f : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hf : Continuous f) (hc : HasCompactSupport f) :
    (∫ x : EuclideanSpace ℝ (Fin 3), ‖f x‖ ^ 2) =
      ∫ w : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
        (∫ r : ℝ in Ioi 0, r ^ 2 * ‖f (r • w.val)‖ ^ 2)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere := by
  simpa only [smul_eq_mul] using integral_polar_dim_three_sphere_outer
    (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3)
    (fun x => ‖f x‖ ^ 2) (compact_norm_sq_integrable hf hc)

theorem compact_coulomb_polar_radius_outer {f : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hf : Continuous f) (hc : HasCompactSupport f)
    (h0 : (0 : EuclideanSpace ℝ (Fin 3)) ∉ tsupport f) :
    (∫ x : EuclideanSpace ℝ (Fin 3), ‖f x‖ ^ 2 / ‖x‖) =
      ∫ r : ℝ in Ioi 0, r *
        (∫ w : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
          ‖f (r • w.val)‖ ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere) := by
  rw [integral_polar_dim_three_radius_outer
    (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3)
    _ (compact_off_zero_norm_sq_div_norm_integrable hf hc h0)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  have hrpos : 0 < r := hr
  have he (w : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
      ‖f (r • w.val)‖ ^ 2 / ‖r • w.val‖ = ‖f (r • w.val)‖ ^ 2 / r := by
    have hw : ‖w.val‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using w.property
    simp [norm_smul, Real.norm_eq_abs, abs_of_pos hrpos, hw]
  simp_rw [he]
  simp_rw [div_eq_mul_inv]
  rw [integral_mul_const]
  simp only [smul_eq_mul]
  field_simp [hrpos.ne']

theorem compact_coulomb_polar_sphere_outer {f : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hf : Continuous f) (hc : HasCompactSupport f)
    (h0 : (0 : EuclideanSpace ℝ (Fin 3)) ∉ tsupport f) :
    (∫ x : EuclideanSpace ℝ (Fin 3), ‖f x‖ ^ 2 / ‖x‖) =
      ∫ w : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
        (∫ r : ℝ in Ioi 0, r * ‖f (r • w.val)‖ ^ 2)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere := by
  rw [integral_polar_dim_three_sphere_outer
    (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3)
    _ (compact_off_zero_norm_sq_div_norm_integrable hf hc h0)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro w
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  have hrpos : 0 < r := hr
  have hw : ‖w.val‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using w.property
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hrpos, hw, mul_one, smul_eq_mul]
  field_simp [hrpos.ne']

end TheoremT.Polar

#print axioms TheoremT.Polar.compact_coulomb_polar_radius_outer
#print axioms TheoremT.Polar.compact_mass_polar_radius_outer
