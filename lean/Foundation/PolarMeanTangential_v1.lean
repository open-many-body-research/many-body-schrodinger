import PhysicalRadialDerivative_v1
import PolarFullEnergy_v1
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The actual physical radial mean has zero tangential derivative. Thus
removing this mean leaves the actual angular kinetic density unchanged. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff BigOperators
namespace TheoremT.Polar

theorem norm_hasFDerivAt_inner {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x : E) (hx : x ≠ 0) :
    HasFDerivAt (fun y : E => ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x := by
  have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))
  simp only [Real.sqrt_sq (norm_nonneg _)] at h
  convert h using 1
  ext v
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  field_simp
  simp [smul_eq_mul, mul_comm]

theorem physicalRadialMean_fderiv_apply {f : EnergyR3 → ℂ}
    (hf : ContDiff ℝ ∞ f) (x v : EnergyR3) (hx : x ≠ 0) :
    fderiv ℝ (physicalRadialMean f) x v =
      (‖x‖⁻¹ * inner ℝ x v) • normalizedRadialDerivativeMean f ‖x‖ := by
  have h := (normalizedRadialMean_hasDerivAt hf ‖x‖).hasFDerivAt.comp x
    (norm_hasFDerivAt_inner x hx)
  have he := congrArg (fun L : EnergyR3 →L[ℝ] ℂ => L v) h.fderiv
  simpa only [physicalRadialMean, Function.comp_def, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply] using! he

theorem physicalRadialMean_fderiv_ray {f : EnergyR3 → ℂ}
    (hf : ContDiff ℝ ∞ f) (w : EnergySphere) {r : ℝ} (hr : 0 < r) (v : EnergyR3) :
    fderiv ℝ (physicalRadialMean f) (r • w.val) v =
      (inner ℝ w.val v) • normalizedRadialDerivativeMean f r := by
  have hw : ‖w.val‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using w.property
  have hx : r • w.val ≠ 0 := by
    apply smul_ne_zero (ne_of_gt hr)
    exact norm_ne_zero_iff.mp (by rw [hw]; norm_num)
  rw [physicalRadialMean_fderiv_apply hf _ _ hx, norm_smul, Real.norm_eq_abs,
    abs_of_pos hr, hw, mul_one, real_inner_smul_left]
  rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hr), one_mul]

theorem physicalRadialMean_tangential_zero {f : EnergyR3 → ℂ}
    (hf : ContDiff ℝ ∞ f) (hz : (0 : EnergyR3) ∉ tsupport f)
    (w : EnergySphere) {r : ℝ} (hr : 0 < r) (i : Fin 3) :
    complexTangentialPartial i (fun y => physicalRadialMean f (r • y)) w.val = 0 := by
  have hw : ‖w.val‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using w.property
  rw [complexTangentialPartial_scaled _
    ((physicalRadialMean_contDiff hf hz).differentiable (by simp)),
    physicalRadialMean_fderiv_ray hf w hr, physicalRadialMean_fderiv_ray hf w hr]
  simp [real_inner_self_eq_norm_sq, hw, EuclideanSpace.inner_single_right]

theorem complexTangentialPartial_sub {f g : EnergyR3 → ℂ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (i : Fin 3) (x : EnergyR3) :
    complexTangentialPartial i (f - g) x =
      complexTangentialPartial i f x - complexTangentialPartial i g x := by
  simp only [complexTangentialPartial, fderiv_sub (hf x) (hg x),
    ContinuousLinearMap.sub_apply, smul_sub]
  abel

theorem physicalFluctuation_tangential_eq {f : EnergyR3 → ℂ}
    (hf : ContDiff ℝ ∞ f) (hz : (0 : EnergyR3) ∉ tsupport f)
    (w : EnergySphere) {r : ℝ} (hr : 0 < r) (i : Fin 3) :
    complexTangentialPartial i (fun y => physicalFluctuation f (r • y)) w.val =
      complexTangentialPartial i (fun y => f (r • y)) w.val := by
  have hs : Differentiable ℝ (fun y : EnergyR3 => r • y) := differentiable_id.const_smul r
  change complexTangentialPartial i
    ((fun y => f (r • y)) - (fun y => physicalRadialMean f (r • y))) w.val = _
  have hF : Differentiable ℝ (fun y : EnergyR3 => f (r • y)) :=
    (hf.differentiable (by simp)).comp hs
  have hM : Differentiable ℝ (fun y : EnergyR3 => physicalRadialMean f (r • y)) :=
    ((physicalRadialMean_contDiff hf hz).differentiable (by simp)).comp hs
  rw [complexTangentialPartial_sub hF hM,
    physicalRadialMean_tangential_zero hf hz w hr, sub_zero]

#print axioms norm_hasFDerivAt_inner
#print axioms physicalRadialMean_fderiv_apply
#print axioms physicalRadialMean_tangential_zero
#print axioms physicalFluctuation_tangential_eq
end TheoremT.Polar
