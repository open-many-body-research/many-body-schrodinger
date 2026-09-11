import PolarMassCoulomb_v1
import PolarMarginalIntegrability_v1

/-! Integrability of both iterated physical mass and nuclear integrals,
discharged from actual compact continuity and support avoiding the nucleus. -/
noncomputable section
open MeasureTheory Set Filter
namespace TheoremT.Polar

theorem compact_mass_radius_marginal_integrable
    {f : EuclideanSpace ℝ (Fin 3) → ℂ} (hf : Continuous f) (hc : HasCompactSupport f) :
    IntegrableOn (fun r : ℝ => r ^ 2 *
      (∫ w : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
        ‖f (r • w.val)‖ ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere)) (Ioi 0) := by
  simpa only [smul_eq_mul] using
    integrable_polar_radius_marginal_dim_three (compact_norm_sq_integrable hf hc)

theorem compact_mass_sphere_marginal_integrable
    {f : EuclideanSpace ℝ (Fin 3) → ℂ} (hf : Continuous f) (hc : HasCompactSupport f) :
    Integrable (fun w : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 =>
      ∫ r : ℝ in Ioi 0, r ^ 2 * ‖f (r • w.val)‖ ^ 2)
      (volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere := by
  simpa only [smul_eq_mul] using
    integrable_polar_sphere_marginal_dim_three (compact_norm_sq_integrable hf hc)

theorem compact_coulomb_radius_marginal_integrable
    {f : EuclideanSpace ℝ (Fin 3) → ℂ} (hf : Continuous f) (hc : HasCompactSupport f)
    (h0 : (0 : EuclideanSpace ℝ (Fin 3)) ∉ tsupport f) :
    IntegrableOn (fun r : ℝ => r *
      (∫ w : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
        ‖f (r • w.val)‖ ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere)) (Ioi 0) := by
  have hi := integrable_polar_radius_marginal_dim_three
    (compact_off_zero_norm_sq_div_norm_integrable hf hc h0)
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have hrpos : 0 < r := hr
  have he (w : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
      ‖f (r • w.val)‖ ^ 2 / ‖r • w.val‖ = ‖f (r • w.val)‖ ^ 2 / r := by
    have hw : ‖w.val‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using w.property
    simp [norm_smul, Real.norm_eq_abs, abs_of_pos hrpos, hw]
  simp_rw [he, div_eq_mul_inv]
  rw [integral_mul_const]
  simp only [smul_eq_mul]
  field_simp [hrpos.ne']

theorem compact_coulomb_sphere_marginal_integrable
    {f : EuclideanSpace ℝ (Fin 3) → ℂ} (hf : Continuous f) (hc : HasCompactSupport f)
    (h0 : (0 : EuclideanSpace ℝ (Fin 3)) ∉ tsupport f) :
    Integrable (fun w : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 =>
      ∫ r : ℝ in Ioi 0, r * ‖f (r • w.val)‖ ^ 2)
      (volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere := by
  have hi := integrable_polar_sphere_marginal_dim_three
    (compact_off_zero_norm_sq_div_norm_integrable hf hc h0)
  apply hi.congr
  apply Eventually.of_forall
  intro w
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  have hrpos : 0 < r := hr
  have hw : ‖w.val‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using w.property
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hrpos, hw, mul_one, smul_eq_mul]
  field_simp [hrpos.ne']

end TheoremT.Polar

#print axioms TheoremT.Polar.compact_coulomb_radius_marginal_integrable
#print axioms TheoremT.Polar.compact_coulomb_sphere_marginal_integrable
