import IntervalPointwiseFTC_v1

/-! Normalized interval averaging form of the actual one-dimensional FTC
estimate. This supplies the one-coordinate premise for finite tensorization. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace TheoremT.Continuum

def intervalAverageMeasure (a b : ℝ) : Measure ℝ :=
  (ENNReal.ofReal (b-a))⁻¹ • volume.restrict (Icc a b)

theorem intervalAverageMeasure_univ {a b : ℝ} (hab : a < b) :
    intervalAverageMeasure a b Set.univ = 1 := by
  have hL : ENNReal.ofReal (b-a) ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab))
  simp only [intervalAverageMeasure,Measure.smul_apply,Measure.restrict_apply_univ,
    Real.volume_Icc,smul_eq_mul]
  exact ENNReal.inv_mul_cancel hL ENNReal.ofReal_ne_top

theorem interval_pointwise_enorm_le_average_derivative
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {a b : ℝ} (hab : a < b) {g dg : ℝ → F}
    (hg : ContinuousOn g (Icc a b)) (hdg : ContinuousOn dg (Icc a b))
    (hd : ∀ t ∈ Icc a b, HasDerivAt g (dg t) t)
    {x : ℝ} (hx : x ∈ Icc a b) :
    ‖g x‖ₑ ≤ (∫⁻ t, ‖g t‖ₑ ∂intervalAverageMeasure a b) +
      ENNReal.ofReal (b-a) * (∫⁻ t, ‖dg t‖ₑ ∂intervalAverageMeasure a b) := by
  have hpos : 0 < b-a := sub_pos.mpr hab
  have hL : ENNReal.ofReal (b-a) ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hpos)
  have hgI : IntegrableOn (fun t => ‖g t‖) (Icc a b) := hg.norm.integrableOn_Icc
  have hdgI : IntegrableOn (fun t => ‖dg t‖) (Icc a b) := hdg.norm.integrableOn_Icc
  have h := ENNReal.ofReal_le_ofReal
    (interval_pointwise_norm_le_average_derivative hab hg hdg hd hx)
  rw [ENNReal.ofReal_add (mul_nonneg (inv_nonneg.mpr hpos.le)
    (intervalIntegral.integral_nonneg hab.le (fun _ _ => norm_nonneg _))) (intervalIntegral.integral_nonneg hab.le
    (fun _ _ => norm_nonneg _)),ENNReal.ofReal_mul (inv_nonneg.mpr hpos.le),
    ENNReal.ofReal_inv_of_pos hpos] at h
  have hi (f : ℝ → F) (hfi : IntegrableOn (fun t => ‖f t‖) (Icc a b)) :
      ENNReal.ofReal (∫ t in a..b, ‖f t‖) = ∫⁻ t in Icc a b, ‖f t‖ₑ := by
    rw [intervalIntegral.integral_of_le hab.le,← integral_Icc_eq_integral_Ioc]
    simpa only [ofReal_norm] using ofReal_integral_eq_lintegral_ofReal hfi
      (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
  rw [hi g hgI,hi dg hdgI,ofReal_norm] at h
  simpa only [intervalAverageMeasure,lintegral_smul_measure,smul_eq_mul,
    ← mul_assoc,ENNReal.mul_inv_cancel hL ENNReal.ofReal_ne_top,one_mul] using h

end TheoremT.Continuum
