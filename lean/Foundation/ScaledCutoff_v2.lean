import HardyWeakCutoff_v1
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Normed.Group.Bounded

/-! Actual scaled compact smooth cutoffs in the physical configuration space.
The derivative bound has a fixed dimension-dependent constant; it is not an
explicit numerical estimate for that constant. No computational claim is made.
-/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace TheoremT.Continuum

def smoothCutoffBase (N : ℕ) : ContDiffBump (0 : Configuration N) :=
  ⟨1, 2, by norm_num, by norm_num⟩

def scaledCutoff (N : ℕ) (R : ℝ) (x : Configuration N) : ℝ :=
  smoothCutoffBase N (R⁻¹ • x)

theorem scaledCutoff_contDiff (N : ℕ) (R : ℝ) :
    ContDiff ℝ ∞ (scaledCutoff N R) :=
  (smoothCutoffBase N).contDiff.comp (contDiff_const_smul R⁻¹)

theorem scaledCutoff_hasCompactSupport (N : ℕ) {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (scaledCutoff N R) :=
  (smoothCutoffBase N).hasCompactSupport.comp_smul (inv_ne_zero hR.ne')

theorem scaledCutoff_nonneg (N : ℕ) (R : ℝ) (x : Configuration N) :
    0 ≤ scaledCutoff N R x := (smoothCutoffBase N).nonneg

theorem scaledCutoff_le_one (N : ℕ) (R : ℝ) (x : Configuration N) :
    scaledCutoff N R x ≤ 1 := (smoothCutoffBase N).le_one

theorem scaledCutoff_norm_le_one (N : ℕ) (R : ℝ) (x : Configuration N) :
    ‖scaledCutoff N R x‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (scaledCutoff_nonneg N R x)]
  exact scaledCutoff_le_one N R x

theorem scaledCutoff_eq_one {N : ℕ} {R : ℝ} (hR : 0 < R)
    {x : Configuration N} (hx : ‖x‖ ≤ R) : scaledCutoff N R x = 1 := by
  apply (smoothCutoffBase N).one_of_mem_closedBall
  change dist (R⁻¹ • x) 0 ≤ (1 : ℝ)
  rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR]
  calc R⁻¹ * ‖x‖ ≤ R⁻¹ * R := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hR.le)
       _ = 1 := inv_mul_cancel₀ hR.ne'

theorem scaledCutoff_eventually_one (N : ℕ) (x : Configuration N) :
    (fun R : ℝ => scaledCutoff N R x) =ᶠ[atTop] (fun _ => 1) := by
  filter_upwards [eventually_ge_atTop (max (‖x‖) 1)] with R hR
  apply scaledCutoff_eq_one
  · exact lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans hR)
  · exact (le_max_left _ _).trans hR

theorem scaledCutoff_tendsto_one (N : ℕ) (x : Configuration N) :
    Tendsto (fun R : ℝ => scaledCutoff N R x) atTop (𝓝 1) :=
  tendsto_const_nhds.congr' (scaledCutoff_eventually_one N x).symm

theorem scaledCutoff_partial (N : ℕ) (R : ℝ) (x : Configuration N)
    (k : Coordinate N) :
    fderiv ℝ (scaledCutoff N R) x (coordinateVector k) =
      R⁻¹ * fderiv ℝ (smoothCutoffBase N) (R⁻¹ • x) (coordinateVector k) := by
  have hbc : ContDiff ℝ ∞ (smoothCutoffBase N) := (smoothCutoffBase N).contDiff
  have hb := (hbc.differentiable (by simp) (R⁻¹ • x)).hasFDerivAt
  have hs := (hasFDerivAt_id (𝕜 := ℝ) x).const_smul R⁻¹
  have hh := hb.comp x hs
  change HasFDerivAt (𝕜 := ℝ) (fun y => smoothCutoffBase N (R⁻¹ • y)) _ x at hh
  change fderiv ℝ (fun y => smoothCutoffBase N (R⁻¹ • y)) x _ = _
  rw [hh.fderiv]
  simp

theorem scaledCutoff_derivative_bound (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∀ (x : Configuration N) (k : Coordinate N),
      ‖fderiv ℝ (scaledCutoff N R) x (coordinateVector k)‖ ≤ C / R := by
  have hbc : ContDiff ℝ ∞ (smoothCutoffBase N) := (smoothCutoffBase N).contDiff
  obtain ⟨C, hC⟩ := ((smoothCutoffBase N).hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    (hbc.continuous_fderiv (by simp))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine ⟨C, hC0, fun R hR x k => ?_⟩
  rw [scaledCutoff_partial, norm_mul, Real.norm_eq_abs R⁻¹, abs_inv, abs_of_pos hR]
  have he : ‖coordinateVector k‖ = 1 := by simp [coordinateVector]
  have hb : ‖(fderiv ℝ (smoothCutoffBase N) (R⁻¹ • x)) (coordinateVector k)‖ ≤ C := by
    calc _ ≤ ‖fderiv ℝ (smoothCutoffBase N) (R⁻¹ • x)‖ * ‖coordinateVector k‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ C := by simpa [he] using hC (R⁻¹ • x)
  simpa [div_eq_mul_inv, mul_comm] using
    mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hR.le)

#print axioms scaledCutoff_contDiff
#print axioms scaledCutoff_hasCompactSupport
#print axioms scaledCutoff_eq_one
#print axioms scaledCutoff_tendsto_one
#print axioms scaledCutoff_derivative_bound
end TheoremT.Continuum
