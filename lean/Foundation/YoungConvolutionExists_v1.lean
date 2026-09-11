import YoungBochnerConvolution_v1

noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped ENNReal
namespace TheoremT.Continuum

theorem young_bochner_smul_integrable_ae {G E : Type*} [MeasurableSpace G] [AddCommGroup G]
    [MeasurableAdd₂ G] [MeasurableNeg G] {μ : Measure G} [SFinite μ]
    [IsAddRightInvariant μ] [IsAddLeftInvariant μ] [IsNegInvariant μ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {K : G → ℝ} {f : G → E} (hK : StronglyMeasurable K) (hf : StronglyMeasurable f)
    {p q r : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hpr : p ≤ r) (hqr : q ≤ r) (hs : 1/p+1/q=1+1/r)
    (hKp : MemLp K (ENNReal.ofReal p) μ) (hfq : MemLp f (ENNReal.ofReal q) μ) :
    ∀ᵐ x ∂μ, Integrable (fun y => K y • f (x-y)) μ := by
  have hI := young_convolution_lintegral_power_le (μ := μ) hK.enorm hf.enorm hp hq hr hpr hqr hs
  have hKfin : (∫⁻ y, ‖K y‖ₑ^p ∂μ)<⊤ := by
    simpa only [ENNReal.toReal_ofReal hp.le] using
      lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (by positivity : ENNReal.ofReal p ≠ 0)
        ENNReal.ofReal_ne_top hKp.eLpNorm_lt_top
  have hffin : (∫⁻ y, ‖f y‖ₑ^q ∂μ)<⊤ := by
    simpa only [ENNReal.toReal_ofReal hq.le] using
      lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (by positivity : ENNReal.ofReal q ≠ 0)
        ENNReal.ofReal_ne_top hfq.eLpNorm_lt_top
  have hfin : (∫⁻ x, (∫⁻ y, ‖K y‖ₑ*‖f (x-y)‖ₑ ∂μ)^r ∂μ)<⊤ :=
    lt_of_le_of_lt hI (ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by positivity) hKfin.ne)
      (ENNReal.rpow_lt_top_of_nonneg (by positivity) hffin.ne))
  have hm : Measurable (fun x => (∫⁻ y, ‖K y‖ₑ*‖f (x-y)‖ₑ ∂μ)^r) := by
    apply Measurable.pow_const
    exact ((hK.enorm.comp measurable_snd).mul
      (hf.enorm.comp (measurable_fst.sub measurable_snd))).lintegral_prod_right'
  filter_upwards [ae_lt_top hm hfin.ne] with x hx
  refine ⟨(hK.smul (hf.comp_measurable (measurable_const.sub measurable_id))).aestronglyMeasurable, ?_⟩
  change (∫⁻ y, ‖K y • f (x-y)‖ₑ ∂μ)<⊤
  simp only [enorm_smul]
  exact (ENNReal.rpow_lt_top_iff_of_pos hr).mp hx

#print axioms young_bochner_smul_integrable_ae
end TheoremT.Continuum
