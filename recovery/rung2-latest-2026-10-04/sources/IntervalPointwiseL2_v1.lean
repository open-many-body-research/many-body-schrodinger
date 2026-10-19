import IntervalPointwiseFTC_v1

/-! The length-explicit one-dimensional point evaluation bound used in the
rectangular tensor FTC argument. It is valid for normed real codomains and
actual derivative fields on the closed interval. -/
noncomputable section
open Set MeasureTheory
namespace TheoremT.Continuum

theorem finite_measure_integral_norm_le_sqrt
    {X F : Type*} [MeasurableSpace X] [NormedAddCommGroup F]
    {mu : Measure X} [IsFiniteMeasure mu] {g : X → F} (hg : MemLp g 2 mu) :
    (∫ x, ‖g x‖ ∂mu) ≤ Real.sqrt ((mu Set.univ).toReal) *
      Real.sqrt (∫ x, ‖g x‖^2 ∂mu) := by
  have h1 : MemLp (fun _ : X => (1 : ℝ)) 2 mu := memLp_const 1
  have hs := actual_l2_integral_inner_sq_le hg.norm h1
  have hsimp : (∫ x, ‖g x‖ ∂mu)^2 ≤
      (∫ x, ‖g x‖^2 ∂mu) * (mu Set.univ).toReal := by
    simpa only [Real.inner_apply,mul_one,norm_norm,norm_one,one_pow,integral_const,
      smul_eq_mul,mul_one,Measure.real] using hs
  apply le_of_sq_le_sq _ (by positivity : 0 ≤ Real.sqrt ((mu Set.univ).toReal) *
      Real.sqrt (∫ x, ‖g x‖^2 ∂mu))
  simpa only [mul_pow,Real.sq_sqrt (ENNReal.toReal_nonneg),
    Real.sq_sqrt (integral_nonneg (fun _ => sq_nonneg _)),mul_comm] using hsimp

theorem interval_integral_norm_le_sqrt
    {F : Type*} [NormedAddCommGroup F] {g : ℝ → F} {a b : ℝ}
    (hab : a ≤ b) (hg : ContinuousOn g (Icc a b)) :
    (∫ t in a..b, ‖g t‖) ≤ Real.sqrt (b-a) * Real.sqrt (∫ t in a..b, ‖g t‖^2) := by
  let mu : Measure ℝ := volume.restrict (Ioc a b)
  have hnormi : Integrable (fun t => ‖g t‖) mu :=
    hg.norm.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hnorm2 : MemLp (fun t => ‖g t‖) 2 mu :=
    (memLp_two_iff_integrable_sq hnormi.aestronglyMeasurable).mpr
      ((hg.norm.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
  have h := finite_measure_integral_norm_le_sqrt hnorm2
  simpa only [norm_norm,mu,Measure.restrict_apply_univ,Real.volume_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab),← intervalIntegral.integral_of_le hab] using h

theorem interval_pointwise_norm_le_L2
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {a b : ℝ} (hab : a < b) {g dg : ℝ → F}
    (hg : ContinuousOn g (Icc a b)) (hdg : ContinuousOn dg (Icc a b))
    (hd : ∀ t ∈ Icc a b, HasDerivAt g (dg t) t)
    {x : ℝ} (hx : x ∈ Icc a b) :
    ‖g x‖ ≤ (Real.sqrt (b-a))⁻¹ * Real.sqrt (∫ t in a..b, ‖g t‖^2) +
      Real.sqrt (b-a) * Real.sqrt (∫ t in a..b, ‖dg t‖^2) := by
  have hL : 0 < b-a := sub_pos.mpr hab
  have hsq : 0 < Real.sqrt (b-a) := Real.sqrt_pos.mpr hL
  have h := (interval_pointwise_norm_le_average_derivative hab hg hdg hd hx).trans
    (add_le_add (mul_le_mul_of_nonneg_left (interval_integral_norm_le_sqrt hab.le hg)
      (inv_nonneg.mpr hL.le)) (interval_integral_norm_le_sqrt hab.le hdg))
  have hid : (b-a)⁻¹ * Real.sqrt (b-a) = (Real.sqrt (b-a))⁻¹ := by
    field_simp
    exact Real.sq_sqrt hL.le
  simpa only [← mul_assoc,hid] using h

end TheoremT.Continuum
