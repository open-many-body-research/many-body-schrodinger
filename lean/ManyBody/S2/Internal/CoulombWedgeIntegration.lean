import ManyBody.S2.Internal.CoulombHeightIntegral
import Mathlib.MeasureTheory.Integral.Prod

/-! The exact Coulomb height integral extends to a justified height/radius Fubini formula. Integrability is proved from a nonnegative radial density and its integrable second moment; the single degenerate radius is a null singleton. No Newton shell or repulsion moment is supplied as a premise. -/

noncomputable section
open MeasureTheory Set
namespace ManyBody.S2.Internal.CoulombAngular

def wedge (s : ℝ) (f : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  {p : ℝ × ℝ | |p.1| < p.2}.indicator
    (fun p => p.2 * f p.2 / Real.sqrt (p.2^2+s^2-2*s*p.1)) p

theorem wedge_eq (s : ℝ) (f : ℝ → ℝ) (z r : ℝ) :
    wedge s f (z,r) = (Ioo (-r) r).indicator
      (fun z => r*f r / Real.sqrt (r^2+s^2-2*s*z)) z := by
  simp only [wedge, indicator_apply, mem_ofPred_eq, mem_Ioo, abs_lt]

theorem wedge_zero_of_nonpos (s : ℝ) (f : ℝ → ℝ) {r : ℝ} (hr : r ≤ 0) :
    (fun z => wedge s f (z,r)) = 0 := by
  funext z
  have h : ¬ |z| < r := not_lt.mpr ((abs_nonneg z).trans' hr)
  simp [wedge,h]

theorem integrable_wedge_slice (s : ℝ) (f : ℝ → ℝ) {r : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hrs : r ≠ s) :
    Integrable (fun z => wedge s f (z,r)) := by
  have hc : ContinuousOn (fun z : ℝ => r*f r / Real.sqrt (r^2+s^2-2*s*z))
      (Icc (-r) r) := by
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro z hz
      exact (Real.sqrt_pos.mpr (kernel_radicand_pos r s hr hs hrs hz)).ne'
  have hi : IntegrableOn (fun z : ℝ => r*f r / Real.sqrt (r^2+s^2-2*s*z)) (Ioo (-r) r) volume :=
    (hc.integrableOn_Icc (μ := volume)).mono_set Ioo_subset_Icc_self
  have hi' := hi.integrable_indicator measurableSet_Ioo
  simpa only [wedge_eq] using hi'

theorem integral_wedge_slice (s : ℝ) (f : ℝ → ℝ) {r : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hrs : r ≠ s) :
    (∫ z : ℝ, wedge s f (z,r)) = 2*r^2*f r / max r s := by
  simp_rw [wedge_eq]
  rw [integral_indicator measurableSet_Ioo]
  simp_rw [div_eq_mul_inv]
  rw [integral_const_mul]
  have hh := integral_coulomb_height r s hr hs hrs
  rw [intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo] at hh
  rw [hh]
  ring

theorem wedge_measurable (s : ℝ) {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (wedge s f) := by
  apply Measurable.indicator
  · exact (measurable_snd.mul (hf.comp measurable_snd)).div
      ((measurable_snd.pow_const 2).add measurable_const |>.sub
        (measurable_const.mul measurable_fst)).sqrt
  · exact measurableSet_lt (continuous_abs.measurable.comp measurable_fst) measurable_snd

#print axioms integral_wedge_slice
#print axioms wedge_measurable

theorem wedge_nonneg (s : ℝ) {f : ℝ → ℝ} (hf : ∀ r, 0 ≤ f r) (p : ℝ × ℝ) :
    0 ≤ wedge s f p := by
  by_cases h : |p.1| < p.2
  · simp only [wedge,indicator_apply,mem_ofPred_eq,ite_eq_left h]
    exact div_nonneg (mul_nonneg ((abs_nonneg _).trans h.le) (hf _)) (Real.sqrt_nonneg _)
  · simp [wedge,h]

theorem integrable_wedge (s : ℝ) (hs : 0 < s) {f : ℝ → ℝ}
    (hfm : Measurable f) (hf : ∀ r, 0 ≤ f r)
    (hfi : IntegrableOn (fun r : ℝ => r^2*f r) (Ioi 0)) :
    Integrable (wedge s f) (volume.prod volume) := by
  have hm := (wedge_measurable s hfm).stronglyMeasurable
  apply (integrable_prod_iff' hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [(volume : Measure ℝ).ae_ne s] with r hrs
    by_cases hr : 0 < r
    · exact integrable_wedge_slice s f hr hs hrs
    · rw [wedge_zero_of_nonpos s f (le_of_not_gt hr)]
      exact integrable_zero ℝ ℝ volume
  · have hdom : Integrable ((Ioi (0 : ℝ)).indicator
        (fun r : ℝ => (2/s)*(r^2*f r))) := by
      rw [integrable_indicator_iff measurableSet_Ioi]
      exact hfi.const_mul (2/s)
    apply hdom.mono' hm.norm.integral_prod_left'.aestronglyMeasurable
    filter_upwards [(volume : Measure ℝ).ae_ne s] with r hrs
    have hnorm : (∫ z : ℝ, ‖wedge s f (z,r)‖) = ∫ z : ℝ, wedge s f (z,r) := by
      apply integral_congr_ae
      filter_upwards [] with z
      exact Real.norm_of_nonneg (wedge_nonneg s hf (z,r))
    rw [hnorm,Real.norm_of_nonneg (integral_nonneg (fun z => wedge_nonneg s hf (z,r)))]
    by_cases hr : 0 < r
    · rw [integral_wedge_slice s f hr hs hrs]
      simp only [indicator_apply,mem_Ioi,ite_eq_left hr]
      calc
        2*r^2*f r/max r s ≤ 2*r^2*f r/s := by
          apply div_le_div_of_nonneg_left (mul_nonneg (by positivity) (hf r)) hs (le_max_right _ _)
        _ = _ := by ring
    · rw [wedge_zero_of_nonpos s f (le_of_not_gt hr)]
      simp [hr]

#print axioms integrable_wedge

theorem integral_wedge (s : ℝ) (hs : 0 < s) {f : ℝ → ℝ}
    (hfm : Measurable f) (hf : ∀ r, 0 ≤ f r)
    (hfi : IntegrableOn (fun r : ℝ => r^2*f r) (Ioi 0)) :
    (∫ z : ℝ, ∫ r : ℝ in Ioi |z|,
      r*f r / Real.sqrt (r^2+s^2-2*s*z)) =
        2 * ∫ r : ℝ in Ioi 0, r^2*f r / max r s := by
  have hi := integrable_wedge s hs hfm hf hfi
  have hz (z : ℝ) :
      (∫ r : ℝ in Ioi |z|, r*f r / Real.sqrt (r^2+s^2-2*s*z)) =
      ∫ r : ℝ, wedge s f (z,r) := by
    rw [← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    filter_upwards [] with r
    simp only [wedge,indicator_apply,mem_Ioi,mem_ofPred_eq]
  simp_rw [hz]
  rw [integral_integral_swap (f := fun z r : ℝ => wedge s f (z,r)) hi]
  rw [← integral_const_mul, ← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards [(volume : Measure ℝ).ae_ne s] with r hrs
  by_cases hr : 0 < r
  · rw [integral_wedge_slice s f hr hs hrs]
    simp only [indicator_apply,mem_Ioi,ite_eq_left hr]
    ring
  · rw [wedge_zero_of_nonpos s f (le_of_not_gt hr)]
    simp [hr]

#print axioms integral_wedge
end ManyBody.S2.Internal.CoulombAngular