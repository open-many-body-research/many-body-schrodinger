import ScaledCutoff_v2
import HardyCutoffBounds_v1
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff InnerProductSpace
namespace TheoremT.Continuum

theorem spatialL2_norm_sq_integral {N : ℕ} (f : SpatialL2 N) :
    ‖f‖^2 = ∫ x, ‖f x‖^2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def,
    ← integral_re (L2.integrable_inner f f)]
  simp [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]

def cutoffAt {N : ℕ} (n : ℕ) (f : SpatialL2 N) : SpatialL2 N :=
  cutoffMul (scaledCutoff N ((n : ℝ)+1)) (scaledCutoff_contDiff N _).continuous
    (scaledCutoff_hasCompactSupport N (by positivity)) f

theorem cutoffAt_ae {N : ℕ} (n : ℕ) (f : SpatialL2 N) :
    cutoffAt n f =ᵐ[volume] (fun x => scaledCutoff N ((n:ℝ)+1) x • f x) :=
  cutoffMul_ae _ _ _ f

theorem cutoffAt_tendsto {N : ℕ} (f : SpatialL2 N) :
    Tendsto (fun n : ℕ => cutoffAt n f) atTop (𝓝 f) := by
  let E : ℕ → Configuration N → ℝ := fun n x =>
    ‖(scaledCutoff N ((n:ℝ)+1) x - 1) • f x‖^2
  have hm (n : ℕ) : AEStronglyMeasurable (E n) volume := by
    exact ((((scaledCutoff_contDiff N _).continuous.sub continuous_const).aestronglyMeasurable.smul
      (Lp.aestronglyMeasurable f)).norm.pow 2)
  have hdom (n : ℕ) : ∀ᵐ x ∂volume, ‖E n x‖ ≤ ‖f x‖^2 := by
    apply Eventually.of_forall
    intro x
    have hc0 := scaledCutoff_nonneg N ((n:ℝ)+1) x
    have hc1 := scaledCutoff_le_one N ((n:ℝ)+1) x
    have ha : ‖scaledCutoff N ((n:ℝ)+1) x - 1‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    change ‖‖(scaledCutoff N ((n:ℝ)+1) x - 1) • f x‖^2‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    apply pow_le_pow_left₀ (norm_nonneg _) _ 2
    simpa only [norm_smul, one_mul] using mul_le_mul_of_nonneg_right ha (norm_nonneg (f x))
  have hi : Integrable (fun x => ‖f x‖^2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  have he (x : Configuration N) : Tendsto (fun n : ℕ => E n x) atTop (𝓝 0) := by
    have hs : Tendsto (fun n : ℕ => (n : ℝ)+1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    have h := (scaledCutoff_tendsto_one N x).comp hs
    simpa only [E, Function.comp_apply, sub_self, zero_smul, norm_zero,
      zero_pow (by decide : 2 ≠ 0)] using
      ((h.sub (tendsto_const_nhds (x := (1 : ℝ)))).smul_const (f x)).norm.pow 2
  have ht : Tendsto (fun n => ∫ x, E n x) atTop (𝓝 0) := by
    simpa only [integral_zero] using tendsto_integral_of_dominated_convergence
      (fun x => ‖f x‖^2) hm hi hdom (Eventually.of_forall he)
  have heq (n : ℕ) : ‖cutoffAt n f - f‖^2 = ∫ x, E n x := by
    rw [spatialL2_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (cutoffAt n f) f, cutoffAt_ae n f] with x hx hc
    rw [hx]
    change ‖cutoffAt n f x - f x‖^2 = _
    rw [hc]
    simp only [E, sub_smul, one_smul]
  have ht2 : Tendsto (fun n => ‖cutoffAt n f - f‖^2) atTop (𝓝 0) := by
    simpa only [heq] using ht
  have ht1 := (Real.continuous_sqrt.tendsto 0).comp ht2
  simp only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] at ht1
  exact tendsto_iff_norm_sub_tendsto_zero.mpr ht1

#print axioms spatialL2_norm_sq_integral
#print axioms cutoffAt_tendsto
end TheoremT.Continuum
