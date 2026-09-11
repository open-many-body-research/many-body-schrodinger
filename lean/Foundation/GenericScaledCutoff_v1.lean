import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

noncomputable section
open Filter
open scoped Topology ContDiff
namespace TheoremT.Continuum
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def genericCutoffBase : ContDiffBump (0 : E) := ⟨1, 2, by norm_num, by norm_num⟩

def genericScaledCutoff (R : ℝ) (x : E) : ℝ := genericCutoffBase E (R⁻¹ • x)

theorem genericScaledCutoff_contDiff (R : ℝ) : ContDiff ℝ ∞ (genericScaledCutoff E R) :=
  (genericCutoffBase E).contDiff.comp (contDiff_const_smul R⁻¹)

theorem genericScaledCutoff_compact {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (genericScaledCutoff E R) :=
  (genericCutoffBase E).hasCompactSupport.comp_smul (inv_ne_zero hR.ne')

theorem genericScaledCutoff_norm_le_one (R : ℝ) (x : E) :
    ‖genericScaledCutoff E R x‖ ≤ 1 := by
  change ‖genericCutoffBase E (R⁻¹ • x)‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg (genericCutoffBase E).nonneg]
  exact (genericCutoffBase E).le_one

theorem genericScaledCutoff_eq_one {R : ℝ} (hR : 0 < R) {x : E} (hx : ‖x‖ ≤ R) :
    genericScaledCutoff E R x = 1 := by
  apply (genericCutoffBase E).one_of_mem_closedBall
  change dist (R⁻¹ • x) 0 ≤ (1 : ℝ)
  rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR]
  calc R⁻¹ * ‖x‖ ≤ R⁻¹ * R := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hR.le)
       _ = 1 := inv_mul_cancel₀ hR.ne'

theorem genericScaledCutoff_eventually_one (x : E) :
    (fun R : ℝ => genericScaledCutoff E R x) =ᶠ[atTop] (fun _ => 1) := by
  filter_upwards [eventually_ge_atTop (max ‖x‖ 1)] with R hR
  exact genericScaledCutoff_eq_one E
    (lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans hR)) ((le_max_left _ _).trans hR)

theorem genericScaledCutoff_partial (R : ℝ) (x v : E) :
    fderiv ℝ (genericScaledCutoff E R) x v =
      R⁻¹ * fderiv ℝ (genericCutoffBase E) (R⁻¹ • x) v := by
  have hbc : ContDiff ℝ ∞ (genericCutoffBase E) := (genericCutoffBase E).contDiff
  have hb := ((hbc.differentiable (by simp)) (R⁻¹ • x)).hasFDerivAt
  have hh := hb.comp x ((hasFDerivAt_id (𝕜 := ℝ) x).const_smul R⁻¹)
  change HasFDerivAt (𝕜 := ℝ) (fun y => genericCutoffBase E (R⁻¹ • y)) _ x at hh
  change fderiv ℝ (fun y => genericCutoffBase E (R⁻¹ • y)) x v = _
  rw [hh.fderiv]
  simp

theorem genericScaledCutoff_partial_bound (v : E) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∀ x : E,
      ‖fderiv ℝ (genericScaledCutoff E R) x v‖ ≤ C / R := by
  have hbc : ContDiff ℝ ∞ (genericCutoffBase E) := (genericCutoffBase E).contDiff
  obtain ⟨C, hC⟩ := ((genericCutoffBase E).hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    (hbc.continuous_fderiv (by simp))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine ⟨C*‖v‖, mul_nonneg hC0 (norm_nonneg _), fun R hR x => ?_⟩
  rw [genericScaledCutoff_partial, norm_mul, Real.norm_eq_abs R⁻¹, abs_inv, abs_of_pos hR]
  have hb : ‖fderiv ℝ (genericCutoffBase E) (R⁻¹ • x) v‖ ≤ C*‖v‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _))
  simpa [div_eq_mul_inv, mul_comm] using mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hR.le)

def genericCutoffBasePartial (v x : E) : ℝ := fderiv ℝ (genericCutoffBase E) x v

theorem genericCutoffBasePartial_contDiff (v : E) :
    ContDiff ℝ ∞ (genericCutoffBasePartial E v) :=
  ((genericCutoffBase E).contDiff.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const

theorem genericScaledCutoff_second (R : ℝ) (x v w : E) :
    fderiv ℝ (fun y => fderiv ℝ (genericScaledCutoff E R) y v) x w =
      R⁻¹^2 * fderiv ℝ (genericCutoffBasePartial E v) (R⁻¹ • x) w := by
  have he : (fun y => fderiv ℝ (genericScaledCutoff E R) y v) =
      fun y => R⁻¹ • genericCutoffBasePartial E v (R⁻¹ • y) := by
    funext y; exact genericScaledCutoff_partial E R y v
  rw [he]
  have hb := ((genericCutoffBasePartial_contDiff E v).differentiable (by simp) (R⁻¹ • x)).hasFDerivAt
  have hh := (hb.comp x ((hasFDerivAt_id (𝕜 := ℝ) x).const_smul R⁻¹)).const_smul R⁻¹
  change HasFDerivAt (𝕜 := ℝ) (fun y => R⁻¹ • genericCutoffBasePartial E v (R⁻¹ • y)) _ x at hh
  rw [hh.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
  ring

theorem genericScaledCutoff_second_bound (v w : E) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∀ x : E,
      ‖fderiv ℝ (fun y => fderiv ℝ (genericScaledCutoff E R) y v) x w‖ ≤ C / R^2 := by
  have hc : HasCompactSupport (genericCutoffBasePartial E v) :=
    (genericCutoffBase E).hasCompactSupport.fderiv_apply ℝ v
  obtain ⟨C, hC⟩ := (hc.fderiv ℝ).exists_bound_of_continuous
    ((genericCutoffBasePartial_contDiff E v).continuous_fderiv (by simp))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine ⟨C*‖w‖, mul_nonneg hC0 (norm_nonneg _), fun R hR x => ?_⟩
  rw [genericScaledCutoff_second, norm_mul, norm_pow, Real.norm_eq_abs R⁻¹,
    abs_inv, abs_of_pos hR]
  have hb : ‖fderiv ℝ (genericCutoffBasePartial E v) (R⁻¹ • x) w‖ ≤ C*‖w‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _))
  simpa only [div_eq_mul_inv, inv_pow, mul_comm] using mul_le_mul_of_nonneg_left hb (sq_nonneg R⁻¹)

#print axioms genericScaledCutoff_second_bound
end TheoremT.Continuum
