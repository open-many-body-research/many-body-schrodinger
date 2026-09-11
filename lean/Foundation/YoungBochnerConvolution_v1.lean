import YoungConvolutionIntegral_v1
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped ENNReal
namespace TheoremT.Continuum

theorem eLpNorm_ofReal_eq_power_integral {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] {μ : Measure X} (f : X → E) {p : ℝ} (hp : 0 < p) :
    eLpNorm f (ENNReal.ofReal p) μ = (∫⁻ x, ‖f x‖ₑ^p ∂μ)^(1/p) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ne_of_gt (ENNReal.ofReal_pos.mpr hp))
    ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp.le]

theorem young_bochner_smul_eLpNorm_le {G E : Type*} [MeasurableSpace G] [AddCommGroup G]
    [MeasurableAdd₂ G] [MeasurableNeg G] {μ : Measure G} [SFinite μ]
    [IsAddRightInvariant μ] [IsAddLeftInvariant μ] [IsNegInvariant μ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {K : G → ℝ} {f : G → E} (hK : StronglyMeasurable K) (hf : StronglyMeasurable f)
    {p q r : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hpr : p ≤ r) (hqr : q ≤ r) (hs : 1/p+1/q=1+1/r) :
    eLpNorm (fun x => ∫ y, K y • f (x-y) ∂μ) (ENNReal.ofReal r) μ ≤
      eLpNorm K (ENNReal.ofReal p) μ * eLpNorm f (ENNReal.ofReal q) μ := by
  have hI : (∫⁻ x, ‖∫ y, K y • f (x-y) ∂μ‖ₑ^r ∂μ) ≤
      (∫⁻ y, ‖K y‖ₑ^p ∂μ)^(r/p)*(∫⁻ y, ‖f y‖ₑ^q ∂μ)^(r/q) := by
    refine le_trans (lintegral_mono fun x => ENNReal.rpow_le_rpow ?_ hr.le)
      (young_convolution_lintegral_power_le hK.enorm hf.enorm
        hp hq hr hpr hqr hs)
    simpa only [enorm_smul] using (enorm_integral_le_lintegral_enorm (fun y => K y • f (x-y)))
  rw [eLpNorm_ofReal_eq_power_integral _ hr,
    eLpNorm_ofReal_eq_power_integral _ hp, eLpNorm_ofReal_eq_power_integral _ hq]
  have ht := ENNReal.rpow_le_rpow hI (show 0 ≤ 1/r by positivity)
  have h1 : (r/p)*(1/r)=1/p := by field_simp
  have h2 : (r/q)*(1/r)=1/q := by field_simp
  simpa only [ENNReal.mul_rpow_of_nonneg _ _ (show 0 ≤ 1/r by positivity),
    ← ENNReal.rpow_mul, h1, h2] using ht

theorem young_bochner_smul_memLp {G E : Type*} [MeasurableSpace G] [AddCommGroup G]
    [MeasurableAdd₂ G] [MeasurableNeg G] {μ : Measure G} [SFinite μ]
    [IsAddRightInvariant μ] [IsAddLeftInvariant μ] [IsNegInvariant μ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {K : G → ℝ} {f : G → E} (hK : StronglyMeasurable K) (hf : StronglyMeasurable f)
    {p q r : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hpr : p ≤ r) (hqr : q ≤ r) (hs : 1/p+1/q=1+1/r)
    (hKp : MemLp K (ENNReal.ofReal p) μ) (hfq : MemLp f (ENNReal.ofReal q) μ) :
    MemLp (fun x => ∫ y, K y • f (x-y) ∂μ) (ENNReal.ofReal r) μ := by
  have hm : StronglyMeasurable (fun z : G×G => K z.2 • f (z.1-z.2)) :=
    (hK.comp_measurable measurable_snd).smul
      (hf.comp_measurable (measurable_fst.sub measurable_snd))
  refine ⟨hm.integral_prod_right'.aestronglyMeasurable, ?_⟩
  exact lt_of_le_of_lt (young_bochner_smul_eLpNorm_le hK hf hp hq hr hpr hqr hs)
    (ENNReal.mul_lt_top hKp.eLpNorm_lt_top hfq.eLpNorm_lt_top)

#print axioms young_bochner_smul_eLpNorm_le
#print axioms young_bochner_smul_memLp
end TheoremT.Continuum
