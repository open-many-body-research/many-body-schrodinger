import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import ActualL2IntegralCauchy_v1

/-! Actual interval point evaluation estimates obtained from FTC and integration.
The interval length is the only geometric constant. No pointwise inequality is
an input; the derivative field is connected by genuine HasDerivAt hypotheses. -/
noncomputable section
open Set MeasureTheory
namespace TheoremT.Continuum
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem interval_norm_sub_le_derivative_integral
    {a b : ℝ} (hab : a ≤ b) {g dg : ℝ → F}
    (hg : ContinuousOn g (Icc a b)) (hdg : ContinuousOn dg (Icc a b))
    (hd : ∀ t ∈ Icc a b, HasDerivAt g (dg t) t)
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    ‖g x-g y‖ ≤ ∫ t in a..b, ‖dg t‖ := by
  have hgap (u v : ℝ) (hu : u ∈ Icc a b) (hv : v ∈ Icc a b) (huv : u ≤ v) :
      ‖g v-g u‖ ≤ ∫ t in a..b, ‖dg t‖ := by
    have hsub : Icc u v ⊆ Icc a b := Icc_subset_Icc hu.1 hv.2
    have hnorm := norm_sub_le_integral_of_norm_deriv_le_of_le huv (hg.mono hsub)
      (fun t ht => (hd t (hsub (Ioo_subset_Icc_self ht))).differentiableAt.differentiableWithinAt)
      (Filter.Eventually.of_forall (fun t ht =>
        le_of_eq (congrArg norm (hd t (hsub (Ioo_subset_Icc_self ht))).deriv)))
      ((hdg.norm.mono hsub).intervalIntegrable_of_Icc huv)
    exact hnorm.trans (intervalIntegral.integral_mono_interval hu.1 huv hv.2
      (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
      (hdg.norm.intervalIntegrable_of_Icc hab))
  rcases le_total y x with hxy | hxy
  · exact hgap y x hy hx hxy
  · rw [norm_sub_rev]
    exact hgap x y hx hy hxy

theorem interval_pointwise_norm_mul_length_le
    {a b : ℝ} (hab : a ≤ b) {g dg : ℝ → F}
    (hg : ContinuousOn g (Icc a b)) (hdg : ContinuousOn dg (Icc a b))
    (hd : ∀ t ∈ Icc a b, HasDerivAt g (dg t) t)
    {x : ℝ} (hx : x ∈ Icc a b) :
    (b-a)*‖g x‖ ≤ (∫ t in a..b, ‖g t‖) + (b-a)*(∫ t in a..b, ‖dg t‖) := by
  have hi : (∫ _y in a..b, ‖g x‖) ≤
      ∫ y in a..b, (‖g y‖ + ∫ t in a..b, ‖dg t‖) :=
    intervalIntegral.integral_mono_on hab (intervalIntegrable_const)
    ((hg.norm.intervalIntegrable_of_Icc hab).add intervalIntegrable_const)
    (fun y hy => (norm_le_norm_add_norm_sub (g y) (g x)).trans
      (add_le_add le_rfl (interval_norm_sub_le_derivative_integral hab hg hdg hd hy hx)))
  rw [intervalIntegral.integral_add (hg.norm.intervalIntegrable_of_Icc hab)
    intervalIntegrable_const] at hi
  simpa only [intervalIntegral.integral_const,smul_eq_mul] using hi

theorem interval_pointwise_norm_le_average_derivative
    {a b : ℝ} (hab : a < b) {g dg : ℝ → F}
    (hg : ContinuousOn g (Icc a b)) (hdg : ContinuousOn dg (Icc a b))
    (hd : ∀ t ∈ Icc a b, HasDerivAt g (dg t) t)
    {x : ℝ} (hx : x ∈ Icc a b) :
    ‖g x‖ ≤ (b-a)⁻¹*(∫ t in a..b, ‖g t‖) + (∫ t in a..b, ‖dg t‖) := by
  have hL : 0 < b-a := sub_pos.mpr hab
  have h := interval_pointwise_norm_mul_length_le hab.le hg hdg hd hx
  apply (mul_le_mul_iff_right₀ hL).mp
  calc
    (b-a)*‖g x‖ ≤ (∫ t in a..b, ‖g t‖)+(b-a)*(∫ t in a..b, ‖dg t‖) := h
    _ = (b-a)*((b-a)⁻¹*(∫ t in a..b, ‖g t‖)+(∫ t in a..b, ‖dg t‖)) := by
      field_simp

end TheoremT.Continuum
