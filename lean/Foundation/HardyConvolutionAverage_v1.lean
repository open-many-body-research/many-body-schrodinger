import HardyConvolutionJensen_v1
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral

/-! L² contraction of convolution against an arbitrary probability measure on an
additive group with a translation-invariant reference measure. This proves the
average estimate from Jensen and Fubini; no Young bound is assumed. -/
noncomputable section
set_option maxHeartbeats 500000
open MeasureTheory
namespace TheoremT.HardyConvolution

/-- Averaging translates is an L² contraction. Strong measurability is an explicit
representative hypothesis. No absolute-continuity assumption on the averaging
probability measure is needed. -/
theorem probability_average_memLp_two_and_bound
    {G E : Type*} [AddCommGroup G] [MeasurableSpace G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ η : Measure G} [SFinite μ] [μ.IsAddRightInvariant] [IsProbabilityMeasure η]
    {f : G → E} (hfM : StronglyMeasurable f) (hf : MemLp f 2 μ) :
    MemLp (fun x => ∫ t, f (x - t) ∂η) 2 μ ∧
      (∫ x, ‖∫ t, f (x - t) ∂η‖^2 ∂μ) ≤ (∫ x, ‖f x‖^2 ∂μ) := by
  have hF : StronglyMeasurable (fun p : G × G => f (p.1 - p.2)) :=
    hfM.comp_measurable (measurable_fst.sub measurable_snd)
  have htrans (t : G) : (∫ x, ‖f (x - t)‖^2 ∂μ) = (∫ x, ‖f x‖^2 ∂μ) :=
    integral_sub_right_eq_self (μ := μ) (fun y => ‖f y‖^2) t
  have hsq : Integrable (fun p : G × G => ‖f (p.1 - p.2)‖^2) (μ.prod η) := by
    apply (integrable_prod_iff' (hF.norm.pow 2).aestronglyMeasurable).2
    constructor
    · apply Filter.Eventually.of_forall
      intro t
      exact (measurePreserving_sub_right μ t).integrable_comp_of_integrable
        (hf.integrable_norm_pow (by norm_num))
    · change Integrable (fun t => ∫ x, ‖‖f (x - t)‖^2‖ ∂μ) η
      simpa only [norm_pow, norm_norm, htrans] using
        (integrable_const (μ := η) (∫ x, ‖f x‖^2 ∂μ))
  have hmean : StronglyMeasurable (fun x => ∫ t, f (x - t) ∂η) :=
    hF.integral_prod_right'
  have hJ : ∀ᵐ x ∂μ,
      ‖∫ t, f (x - t) ∂η‖^2 ≤ ∫ t, ‖f (x - t)‖^2 ∂η := by
    filter_upwards [hsq.prod_right_ae] with x hx
    apply norm_integral_sq_le_integral_norm_sq
    apply (memLp_two_iff_integrable_sq_norm
      (hfM.comp_measurable (measurable_const.sub measurable_id)).aestronglyMeasurable).2
    exact hx
  have hmeanSq : Integrable (fun x => ‖∫ t, f (x - t) ∂η‖^2) μ :=
    hsq.integral_prod_left.mono_nonneg (hmean.norm.pow 2).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _)) hJ
  constructor
  · exact (memLp_two_iff_integrable_sq_norm hmean.aestronglyMeasurable).2 hmeanSq
  · calc
      (∫ x, ‖∫ t, f (x - t) ∂η‖^2 ∂μ) ≤
          ∫ x, (∫ t, ‖f (x - t)‖^2 ∂η) ∂μ :=
        integral_mono_ae hmeanSq hsq.integral_prod_left hJ
      _ = ∫ t, (∫ x, ‖f (x - t)‖^2 ∂μ) ∂η := integral_integral_swap hsq
      _ = ∫ x, ‖f x‖^2 ∂μ := by simp only [htrans, integral_const, probReal_univ, one_smul]

set_option pp.proofs false in
#print probability_average_memLp_two_and_bound
#print axioms probability_average_memLp_two_and_bound
end TheoremT.HardyConvolution
