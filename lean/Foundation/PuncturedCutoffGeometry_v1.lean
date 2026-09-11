import ScaledCutoff_v2
import Mathlib.Analysis.SpecificLimits.Basic

/-! Shrinking cutoffs and their derivative support in the actual configuration space.
These statements are pointwise; the puncture is explicitly excluded where division
by its distance is used. No dimension-dependent capacity assertion occurs here. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace TheoremT.Continuum

def punctureRadius (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem punctureRadius_pos (n : ℕ) : 0 < punctureRadius n := by
  unfold punctureRadius
  positivity

theorem punctureRadius_tendsto : Tendsto punctureRadius atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem scaledCutoff_eq_zero_of_two_mul_le {N : ℕ} {R : ℝ} (hR : 0 < R)
    {x : Configuration N} (hx : 2 * R ≤ ‖x‖) : scaledCutoff N R x = 0 := by
  apply (smoothCutoffBase N).zero_of_le_dist
  change (2 : ℝ) ≤ dist (R⁻¹ • x) 0
  rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR]
  calc (2 : ℝ) = R⁻¹ * (2 * R) := by field_simp
       _ ≤ R⁻¹ * ‖x‖ := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hR.le)

theorem scaledCutoff_partial_eq_zero_of_two_mul_lt {N : ℕ} {R : ℝ} (hR : 0 < R)
    {x : Configuration N} (hx : 2 * R < ‖x‖) (k : Coordinate N) :
    fderiv ℝ (scaledCutoff N R) x (coordinateVector k) = 0 := by
  rw [scaledCutoff_partial]
  have hn : R⁻¹ • x ∉ tsupport (smoothCutoffBase N) := by
    rw [(smoothCutoffBase N).tsupport_eq]
    change ¬ dist (R⁻¹ • x) 0 ≤ (2 : ℝ)
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR]
    apply not_le.mpr
    calc (2 : ℝ) = R⁻¹ * (2 * R) := by field_simp
         _ < R⁻¹ * ‖x‖ := mul_lt_mul_of_pos_left hx (inv_pos.mpr hR)
  rw [fderiv_of_notMem_tsupport ℝ hn]
  simp

theorem shrinkingCutoff_eventually_zero {N : ℕ} {x : Configuration N} (hx : x ≠ 0) :
    (fun n => scaledCutoff N (punctureRadius n) x) =ᶠ[atTop] (fun _ => 0) := by
  have ht : Tendsto (fun n => 2 * punctureRadius n) atTop (𝓝 0) := by
    simpa using punctureRadius_tendsto.const_mul 2
  filter_upwards [ht.eventually (gt_mem_nhds (norm_pos_iff.mpr hx))] with n hn
  exact scaledCutoff_eq_zero_of_two_mul_le (punctureRadius_pos n) hn.le

theorem shrinkingCutoff_partial_eventually_zero {N : ℕ} {x : Configuration N}
    (hx : x ≠ 0) (k : Coordinate N) :
    (fun n => fderiv ℝ (scaledCutoff N (punctureRadius n)) x (coordinateVector k))
      =ᶠ[atTop] (fun _ => 0) := by
  have ht : Tendsto (fun n => 2 * punctureRadius n) atTop (𝓝 0) := by
    simpa using punctureRadius_tendsto.const_mul 2
  filter_upwards [ht.eventually (gt_mem_nhds (norm_pos_iff.mpr hx))] with n hn
  exact scaledCutoff_partial_eq_zero_of_two_mul_lt (punctureRadius_pos n) hn k

theorem scaledCutoff_partial_inverse_distance_bound (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∀ (x : Configuration N), x ≠ 0 →
      ∀ k : Coordinate N,
      ‖fderiv ℝ (scaledCutoff N R) x (coordinateVector k)‖ ≤ (2 * C) / ‖x‖ := by
  obtain ⟨C, hC, hb⟩ := scaledCutoff_derivative_bound N
  refine ⟨C, hC, fun R hR x hx k => ?_⟩
  by_cases hxr : 2 * R < ‖x‖
  · rw [scaledCutoff_partial_eq_zero_of_two_mul_lt hR hxr k, norm_zero]
    positivity
  · have hxR : ‖x‖ ≤ 2 * R := le_of_not_gt hxr
    apply (hb R hR x k).trans
    apply (div_le_div_iff₀ hR (norm_pos_iff.mpr hx)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hxR hC]

#print axioms scaledCutoff_eq_zero_of_two_mul_le
#print axioms scaledCutoff_partial_eq_zero_of_two_mul_lt
#print axioms shrinkingCutoff_eventually_zero
#print axioms shrinkingCutoff_partial_eventually_zero
#print axioms scaledCutoff_partial_inverse_distance_bound
end TheoremT.Continuum
