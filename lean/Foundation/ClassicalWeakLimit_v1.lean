import HardyWeakCore_v1
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Compact-test dominated convergence produces derivatives in the unchanged
weak Sobolev definition. No classical regularity of the limiting function is
assumed, and no approximate derivative is silently identified with a weak one. -/
noncomputable section
set_option maxHeartbeats 1600000
open MeasureTheory Filter
open scoped Topology ContDiff
namespace TheoremT.Continuum

theorem compact_test_integral_tendsto_dominated {N : ℕ}
    {u : ℕ → Configuration N → ℂ} {f : Configuration N → ℂ}
    {bound : Configuration N → ℝ} (hb : MemLp bound 2 volume)
    (hu : ∀ n, AEStronglyMeasurable (u n) volume)
    (hbound : ∀ n, ∀ᵐ x ∂volume, ‖u n x‖ ≤ ‖bound x‖)
    (hlim : ∀ᵐ x ∂volume, Tendsto (fun n => u n x) atTop (𝓝 (f x)))
    {φ : Configuration N → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    Tendsto (fun n => ∫ x, φ x • u n x) atTop (𝓝 (∫ x, φ x • f x)) := by
  have hbi : Integrable (fun x => ‖φ x‖ * ‖bound x‖) volume := by
    simpa only [smul_eq_mul] using
      (hb.norm.locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
        hφ.norm hc.norm
  apply tendsto_integral_of_dominated_convergence (fun x => ‖φ x‖ * ‖bound x‖)
  · intro n
    exact hφ.aestronglyMeasurable.smul (hu n)
  · exact hbi
  · intro n
    filter_upwards [hbound n] with x hx
    simpa only [norm_smul] using mul_le_mul_of_nonneg_left hx (norm_nonneg (φ x))
  · filter_upwards [hlim] with x hx
    exact tendsto_const_nhds.smul hx

theorem weakPartial_of_classical_dominated_limit {N : ℕ}
    {u : ℕ → Configuration N → ℂ} {f g : Configuration N → ℂ}
    {k : Coordinate N} (hu : ∀ n, ContDiff ℝ 1 (u n))
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    {boundF boundG : Configuration N → ℝ}
    (hBF : MemLp boundF 2 volume) (hBG : MemLp boundG 2 volume)
    (hboundF : ∀ n, ∀ᵐ x ∂volume, ‖u n x‖ ≤ ‖boundF x‖)
    (hboundG : ∀ n, ∀ᵐ x ∂volume,
      ‖fderiv ℝ (u n) x (coordinateVector k)‖ ≤ ‖boundG x‖)
    (hlimF : ∀ᵐ x ∂volume, Tendsto (fun n => u n x) atTop (𝓝 (f x)))
    (hlimG : ∀ᵐ x ∂volume,
      Tendsto (fun n => fderiv ℝ (u n) x (coordinateVector k)) atTop (𝓝 (g x))) :
    WeakPartial (hf.toLp f) (hg.toLp g) k := by
  intro φ hφ hc
  have hdφ : Continuous (fun x => fderiv ℝ φ x (coordinateVector k)) :=
    (hφ.continuous_fderiv_apply (by norm_num)).comp (continuous_id.prodMk continuous_const)
  have hd (n : ℕ) : Continuous (fun x => fderiv ℝ (u n) x (coordinateVector k)) :=
    ((hu n).continuous_fderiv_apply (by norm_num)).comp
      (continuous_id.prodMk continuous_const)
  have heq (n : ℕ) :
      (∫ x, φ x • fderiv ℝ (u n) x (coordinateVector k)) =
        -(∫ x, fderiv ℝ φ x (coordinateVector k) • u n x) := by
    apply integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
    · exact (hdφ.smul (hu n).continuous).integrable_of_hasCompactSupport
        (hc.fderiv_apply ℝ (coordinateVector k)).smul_right
    · exact (hφ.continuous.smul (hd n)).integrable_of_hasCompactSupport hc.smul_right
    · exact (hφ.continuous.smul (hu n).continuous).integrable_of_hasCompactSupport hc.smul_right
    · intro x _
      exact hφ.differentiable (by norm_num) x
    · intro x _
      exact (hu n).differentiable (by norm_num) x
  have hl := compact_test_integral_tendsto_dominated hBG
    (fun n => (hd n).aestronglyMeasurable) hboundG hlimG hφ.continuous hc
  have hr := (compact_test_integral_tendsto_dominated hBF
    (fun n => (hu n).continuous.aestronglyMeasurable) hboundF hlimF hdφ
      (hc.fderiv_apply ℝ (coordinateVector k))).neg
  have he : (∫ x, φ x • g x) = -(∫ x, fderiv ℝ φ x (coordinateVector k) • f x) :=
    tendsto_nhds_unique hl (hr.congr' (Eventually.of_forall (fun n => (heq n).symm)))
  calc
    _ = ∫ x, φ x • g x := by
      apply integral_congr_ae
      filter_upwards [hg.coeFn_toLp] with x hx
      rw [hx]
    _ = -(∫ x, fderiv ℝ φ x (coordinateVector k) • f x) := he
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with x hx
      rw [hx]

#print axioms compact_test_integral_tendsto_dominated
#print axioms weakPartial_of_classical_dominated_limit
end TheoremT.Continuum
