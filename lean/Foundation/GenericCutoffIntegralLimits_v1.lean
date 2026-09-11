import GenericCutoffLimits_v1
import Mathlib.MeasureTheory.Function.LocallyIntegrable

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace TheoremT.Continuum
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem generic_cutoff_integral_limit {g : E → ℂ} (hg : Integrable g volume) :
    Tendsto (fun n : ℕ => ∫ x, genericScaledCutoff E ((n : ℝ)+1) x • g x)
      atTop (𝓝 (∫ x, g x)) := by
  simpa only [one_smul] using bounded_real_multiplier_integral_tendsto hg
    (fun n => (genericScaledCutoff_contDiff E _).continuous.aestronglyMeasurable)
    (fun n => Eventually.of_forall (genericScaledCutoff_norm_le_one E _))
    (Eventually.of_forall (genericScaledCutoff_sequence_tendsto_one E))

theorem generic_cutoff_first_integral_limit {g : E → ℂ} (hg : Integrable g volume) (v : E) :
    Tendsto (fun n : ℕ => ∫ x, fderiv ℝ (genericScaledCutoff E ((n : ℝ)+1)) x v • g x)
      atTop (𝓝 0) := by
  obtain ⟨C,hC,hb,ht⟩ := genericScaledCutoff_first_sequence E v
  have hm (n : ℕ) : AEStronglyMeasurable
      (fun x => fderiv ℝ (genericScaledCutoff E ((n : ℝ)+1)) x v) volume :=
    (((genericScaledCutoff_contDiff E _).continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable
  simpa only [zero_smul, integral_zero] using bounded_real_multiplier_integral_tendsto hg hm
    (fun n => Eventually.of_forall (hb n)) (Eventually.of_forall ht)

theorem generic_cutoff_second_integral_limit {g : E → ℂ} (hg : Integrable g volume) (v w : E) :
    Tendsto (fun n : ℕ => ∫ x,
      fderiv ℝ (fun y => fderiv ℝ (genericScaledCutoff E ((n : ℝ)+1)) y v) x w • g x)
      atTop (𝓝 0) := by
  obtain ⟨C,hC,hb,ht⟩ := genericScaledCutoff_second_sequence E v w
  have hd (n : ℕ) : ContDiff ℝ ∞
      (fun y => fderiv ℝ (genericScaledCutoff E ((n : ℝ)+1)) y v) :=
    ((genericScaledCutoff_contDiff E _).fderiv_right
      (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  have hm (n : ℕ) : AEStronglyMeasurable (fun x =>
      fderiv ℝ (fun y => fderiv ℝ (genericScaledCutoff E ((n : ℝ)+1)) y v) x w) volume :=
    (((hd n).continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable
  simpa only [zero_smul, integral_zero] using bounded_real_multiplier_integral_tendsto hg hm
    (fun n => Eventually.of_forall (hb n)) (Eventually.of_forall ht)

#print axioms generic_cutoff_second_integral_limit
end TheoremT.Continuum
