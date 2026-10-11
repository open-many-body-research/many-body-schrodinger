import BoundedExponentialWeights_v1
import BoundedSmoothMultiplier_v1

/-! Comparisons between physical, smooth-radius and bounded exponential weights
on actual L² functions. No integration procedure or computable norm is claimed. -/
noncomputable section
open MeasureTheory Filter
namespace TheoremT.Continuum

theorem physical_exponential_memLp_of_smooth {N : ℕ} {a : ℝ} (ha : 0 ≤ a)
    (f : SpatialL2 N)
    (hw : MemLp (fun x => Real.exp (a*smoothConfigurationRadius N x) • f x) 2 volume) :
    MemLp (fun x => Real.exp (a*‖x‖) • f x) 2 volume := by
  apply hw.of_le
    ((Real.continuous_exp.comp (continuous_const.mul continuous_norm)).aestronglyMeasurable.smul
      (Lp.aestronglyMeasurable f))
  exact Eventually.of_forall (fun x => by
    change ‖Real.exp (a*‖x‖) • f x‖ ≤ ‖Real.exp (a*smoothConfigurationRadius N x) • f x‖
    simp only [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
        (norm_le_smoothConfigurationRadius x) ha)) (norm_nonneg (f x)))

theorem smooth_exponential_memLp_of_physical {N : ℕ} {a : ℝ} (ha : 0 ≤ a)
    (f : SpatialL2 N)
    (hw : MemLp (fun x => Real.exp (a*‖x‖) • f x) 2 volume) :
    MemLp (fun x => Real.exp (a*smoothConfigurationRadius N x) • f x) 2 volume := by
  apply (hw.const_smul (Real.exp a)).of_le
    ((Real.continuous_exp.comp (continuous_const.mul
      (smoothConfigurationRadius_contDiff N).continuous)).aestronglyMeasurable.smul
        (Lp.aestronglyMeasurable f))
  exact Eventually.of_forall (fun x => by
    change ‖Real.exp (a*smoothConfigurationRadius N x) • f x‖ ≤
      ‖Real.exp a • (Real.exp (a*‖x‖) • f x)‖
    simp only [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    rw [← mul_assoc,← Real.exp_add]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by
      have h := mul_le_mul_of_nonneg_left (smoothConfigurationRadius_le_norm_add_one x) ha
      nlinarith)) (norm_nonneg (f x)))

theorem boundedExpWeight_mul_norm_le {N : ℕ} (a : ℝ) {L : ℝ} (hL : 0 < L)
    (f : SpatialL2 N)
    (hw : MemLp (fun x => Real.exp (a*smoothConfigurationRadius N x) • f x) 2 volume) :
    ‖boundedRealMul (boundedExpWeight N a L) (boundedExpWeight_memLp_top N a hL) f‖ ≤
      ‖hw.toLp (fun x => Real.exp (a*smoothConfigurationRadius N x) • f x)‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [boundedRealMul_ae (boundedExpWeight N a L)
    (boundedExpWeight_memLp_top N a hL) f,hw.coeFn_toLp] with x hx hy
  rw [hx,hy]
  simp only [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),
    abs_of_pos (boundedExpWeight_pos N a hL x)]
  exact mul_le_mul_of_nonneg_right (boundedExpWeight_le_exp N a hL x) (norm_nonneg (f x))

#print axioms physical_exponential_memLp_of_smooth
#print axioms smooth_exponential_memLp_of_physical
#print axioms boundedExpWeight_mul_norm_le
end TheoremT.Continuum
