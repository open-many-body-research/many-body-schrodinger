import PolarMassCoulomb_v1
import PolarMarginalIntegrability_v1

/-! Actual inverse-square moment and its polar marginals. The input is a
continuous compactly supported complex function on Euclidean R3 whose closed
support avoids the origin. All integrability assertions are derived. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace TheoremT.Polar

theorem compact_off_zero_norm_sq_div_norm_sq_continuous
    {f : EuclideanSpace ℝ (Fin 3) → ℂ} (hf : Continuous f)
    (h0 : (0 : EuclideanSpace ℝ (Fin 3)) ∉ tsupport f) :
    Continuous (fun x => ‖f x‖ ^ 2 / ‖x‖ ^ 2) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst x
    apply (continuousAt_const : ContinuousAt
      (fun _ : EuclideanSpace ℝ (Fin 3) => (0 : ℝ)) 0).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds h0] with y hy
    simp [image_eq_zero_of_notMem_tsupport hy]
  · exact (hf.norm.pow 2).continuousAt.div (continuous_norm.pow 2).continuousAt
      (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))

theorem compact_off_zero_norm_sq_div_norm_sq_integrable
    {f : EuclideanSpace ℝ (Fin 3) → ℂ} (hf : Continuous f) (hc : HasCompactSupport f)
    (h0 : (0 : EuclideanSpace ℝ (Fin 3)) ∉ tsupport f) :
    Integrable (fun x => ‖f x‖ ^ 2 / ‖x‖ ^ 2) := by
  have hcomp : HasCompactSupport (fun x => ‖f x‖ ^ 2 / ‖x‖ ^ 2) := by
    rw [hasCompactSupport_iff_eventuallyEq] at hc ⊢
    filter_upwards [hc] with x hx
    simp [hx]
  exact (compact_off_zero_norm_sq_div_norm_sq_continuous hf h0).integrable_of_hasCompactSupport hcomp

theorem inverseSquare_radial_weight_cancel (f : EuclideanSpace ℝ (Fin 3) → ℂ)
    {r : ℝ} (hr : 0 < r) (w : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    r ^ 2 * (‖f (r • w.val)‖ ^ 2 / ‖r • w.val‖ ^ 2) = ‖f (r • w.val)‖ ^ 2 := by
  have hw : ‖w.val‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using w.property
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hw, mul_one]
  field_simp [hr.ne']

theorem compact_inverseSquare_polar_radius_outer
    {f : EuclideanSpace ℝ (Fin 3) → ℂ} (hf : Continuous f) (hc : HasCompactSupport f)
    (h0 : (0 : EuclideanSpace ℝ (Fin 3)) ∉ tsupport f) :
    (∫ x : EuclideanSpace ℝ (Fin 3), ‖f x‖ ^ 2 / ‖x‖ ^ 2) =
      ∫ r : ℝ in Ioi 0, ∫ w : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
        ‖f (r • w.val)‖ ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere := by
  rw [integral_polar_dim_three_radius_outer
    (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3)
    _ (compact_off_zero_norm_sq_div_norm_sq_integrable hf hc h0)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  simp only [smul_eq_mul]
  rw [← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall (inverseSquare_radial_weight_cancel f hr))

theorem compact_inverseSquare_polar_sphere_outer
    {f : EuclideanSpace ℝ (Fin 3) → ℂ} (hf : Continuous f) (hc : HasCompactSupport f)
    (h0 : (0 : EuclideanSpace ℝ (Fin 3)) ∉ tsupport f) :
    (∫ x : EuclideanSpace ℝ (Fin 3), ‖f x‖ ^ 2 / ‖x‖ ^ 2) =
      ∫ w : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
        (∫ r : ℝ in Ioi 0, ‖f (r • w.val)‖ ^ 2)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere := by
  rw [integral_polar_dim_three_sphere_outer
    (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3)
    _ (compact_off_zero_norm_sq_div_norm_sq_integrable hf hc h0)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro w
  exact setIntegral_congr_fun measurableSet_Ioi (fun r hr => inverseSquare_radial_weight_cancel f hr w)

theorem compact_inverseSquare_radius_marginal_integrable
    {f : EuclideanSpace ℝ (Fin 3) → ℂ} (hf : Continuous f) (hc : HasCompactSupport f)
    (h0 : (0 : EuclideanSpace ℝ (Fin 3)) ∉ tsupport f) :
    IntegrableOn (fun r : ℝ => ∫ w : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      ‖f (r • w.val)‖ ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere) (Ioi 0) := by
  have hi := integrable_polar_radius_marginal_dim_three
    (compact_off_zero_norm_sq_div_norm_sq_integrable hf hc h0)
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  simp only [smul_eq_mul]
  rw [← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall (inverseSquare_radial_weight_cancel f hr))

theorem compact_inverseSquare_sphere_marginal_integrable
    {f : EuclideanSpace ℝ (Fin 3) → ℂ} (hf : Continuous f) (hc : HasCompactSupport f)
    (h0 : (0 : EuclideanSpace ℝ (Fin 3)) ∉ tsupport f) :
    Integrable (fun w : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 =>
      ∫ r : ℝ in Ioi 0, ‖f (r • w.val)‖ ^ 2)
      (volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere := by
  have hi := integrable_polar_sphere_marginal_dim_three
    (compact_off_zero_norm_sq_div_norm_sq_integrable hf hc h0)
  apply hi.congr
  apply Eventually.of_forall
  intro w
  exact setIntegral_congr_fun measurableSet_Ioi (fun r hr => inverseSquare_radial_weight_cancel f hr w)

end TheoremT.Polar

#print axioms TheoremT.Polar.compact_inverseSquare_polar_radius_outer
#print axioms TheoremT.Polar.compact_inverseSquare_sphere_marginal_integrable
