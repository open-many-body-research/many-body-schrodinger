import YoungBochnerConvolution_v1

noncomputable section
open MeasureTheory MeasureTheory.Measure Filter
open scoped ENNReal
namespace TheoremT.Continuum

theorem holder_bochner_smul_enorm_le {G E : Type*} [MeasurableSpace G] [AddCommGroup G]
    [MeasurableAdd₂ G] [MeasurableNeg G] {μ : Measure G}
    [IsAddLeftInvariant μ] [IsNegInvariant μ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {K : G → ℝ} {f : G → E} (hK : StronglyMeasurable K) (hf : StronglyMeasurable f)
    {p q : ℝ} (hpq : p.HolderConjugate q) (x : G) :
    ‖∫ y, K y • f (x-y) ∂μ‖ₑ ≤
      eLpNorm K (ENNReal.ofReal p) μ * eLpNorm f (ENNReal.ofReal q) μ := by
  have hm : AEMeasurable (fun y => ‖f (x-y)‖ₑ) μ :=
    (hf.enorm.comp (measurable_const.sub measurable_id)).aemeasurable
  have ht := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hK.enorm.aemeasurable hm
  have he : (∫⁻ y, ‖f (x-y)‖ₑ^q ∂μ)=(∫⁻ y, ‖f y‖ₑ^q ∂μ) :=
    lintegral_sub_left_eq_self (fun y => ‖f y‖ₑ^q) x
  rw [eLpNorm_ofReal_eq_power_integral _ hpq.pos,
    eLpNorm_ofReal_eq_power_integral _ hpq.symm.pos]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  simpa only [enorm_smul,Pi.mul_apply,he] using ht

theorem holder_bochner_smul_memLp_top {G E : Type*} [MeasurableSpace G] [AddCommGroup G]
    [MeasurableAdd₂ G] [MeasurableNeg G] {μ : Measure G} [SFinite μ]
    [IsAddLeftInvariant μ] [IsNegInvariant μ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {K : G → ℝ} {f : G → E} (hK : StronglyMeasurable K) (hf : StronglyMeasurable f)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (hKp : MemLp K (ENNReal.ofReal p) μ) (hfq : MemLp f (ENNReal.ofReal q) μ) :
    MemLp (fun x => ∫ y, K y • f (x-y) ∂μ) ⊤ μ := by
  have hm : StronglyMeasurable (fun z : G×G => K z.2 • f (z.1-z.2)) :=
    (hK.comp_measurable measurable_snd).smul
      (hf.comp_measurable (measurable_fst.sub measurable_snd))
  refine ⟨hm.integral_prod_right'.aestronglyMeasurable, ?_⟩
  rw [eLpNorm_exponent_top]
  exact (eLpNormEssSup_le_of_ae_enorm_bound (Eventually.of_forall
    (holder_bochner_smul_enorm_le hK hf hpq))).trans_lt
    (ENNReal.mul_lt_top hKp.eLpNorm_lt_top hfq.eLpNorm_lt_top)

#print axioms holder_bochner_smul_memLp_top
end TheoremT.Continuum
