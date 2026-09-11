import NonlinearWeakChainCore_v1
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! Smooth norm regularization on the complex plane as a real Hilbert space.
The first derivative bound is uniform as the positive regularizer tends to zero. -/
noncomputable section
open scoped ContDiff RealInnerProductSpace
namespace TheoremT.Continuum

def regularizedComplexNorm (ε : ℝ) (z : ℂ) : ℂ :=
  ((Real.sqrt (ε^2+‖z‖^2)-ε : ℝ) : ℂ)

theorem regularizedComplexNorm_contDiff {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ ∞ (regularizedComplexNorm ε) := by
  exact Complex.ofRealCLM.contDiff.comp
    (((contDiff_const.add (contDiff_norm_sq ℝ)).sqrt
      (fun z => by positivity : ∀ z : ℂ, ε^2+‖z‖^2 ≠ 0)).sub contDiff_const)

theorem regularizedComplexNorm_zero {ε : ℝ} (hε : 0 < ε) :
    regularizedComplexNorm ε 0 = 0 := by
  simp [regularizedComplexNorm,Real.sqrt_sq hε.le]

theorem regularizedComplexNorm_fderiv {ε : ℝ} (hε : 0 < ε) (z w : ℂ) :
    fderiv ℝ (regularizedComplexNorm ε) z w =
      ((inner ℝ z w / Real.sqrt (ε^2+‖z‖^2) : ℝ) : ℂ) := by
  have hh := ((hasStrictFDerivAt_norm_sq z).hasFDerivAt.const_add (ε^2)).sqrt
    (by positivity : ε^2+‖z‖^2 ≠ 0)
  have hj := Complex.ofRealCLM.hasFDerivAt.comp z (hh.sub_const ε)
  change HasFDerivAt (regularizedComplexNorm ε) _ z at hj
  rw [hj.fderiv]
  simp only [ContinuousLinearMap.comp_apply,Complex.ofRealCLM_apply,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.add_apply,
    innerSL_apply_apply,smul_eq_mul,two_smul]
  congr 1
  ring

theorem regularizedComplexNorm_fderiv_norm {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    ‖fderiv ℝ (regularizedComplexNorm ε) z‖ ≤ 1 := by
  have hp : 0 < Real.sqrt (ε^2+‖z‖^2) := Real.sqrt_pos.mpr (by positivity)
  have hs := Real.sq_sqrt (show 0 ≤ ε^2+‖z‖^2 by positivity)
  have hz : ‖z‖ ≤ Real.sqrt (ε^2+‖z‖^2) := by nlinarith [norm_nonneg z]
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro w
  rw [regularizedComplexNorm_fderiv hε,Complex.norm_real,Real.norm_eq_abs,
    abs_div,abs_of_pos hp,one_mul]
  apply (div_le_iff₀ hp).mpr
  exact (abs_real_inner_le_norm z w).trans (by nlinarith [norm_nonneg w])

theorem regularizedComplexNorm_norm_le {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    ‖regularizedComplexNorm ε z‖ ≤ ‖z‖ := by
  have hp : 0 ≤ Real.sqrt (ε^2+‖z‖^2) := Real.sqrt_nonneg _
  have hs := Real.sq_sqrt (show 0 ≤ ε^2+‖z‖^2 by positivity)
  have he : ε ≤ Real.sqrt (ε^2+‖z‖^2) := by nlinarith [norm_nonneg z]
  have hu : Real.sqrt (ε^2+‖z‖^2) ≤ ‖z‖+ε := by nlinarith [norm_nonneg z]
  simpa only [regularizedComplexNorm,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr he)] using (sub_le_iff_le_add.mpr hu)

#print axioms regularizedComplexNorm_contDiff
#print axioms regularizedComplexNorm_fderiv
#print axioms regularizedComplexNorm_fderiv_norm
#print axioms regularizedComplexNorm_norm_le
end TheoremT.Continuum
