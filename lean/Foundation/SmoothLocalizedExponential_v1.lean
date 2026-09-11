import SmoothRealDerivativeSums_v1

/-! Exact first and mixed derivatives of chi exp(-F), with compactness inherited
from chi. This is the smooth algebra used before taking Coulomb cusp limits. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum

theorem smooth_localized_exp_contDiff {N : ℕ} {χ F : Configuration N → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun x => χ x*Real.exp (-F x)) := hχ.mul hF.neg.exp

theorem smooth_localized_exp_compact {N : ℕ} {χ F : Configuration N → ℝ}
    (hc : HasCompactSupport χ) : HasCompactSupport (fun x => χ x*Real.exp (-F x)) := hc.mul_right

theorem smooth_localized_exp_partial {N : ℕ} {χ F : Configuration N → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hF : ContDiff ℝ ∞ F) (x v : Configuration N) :
    fderiv ℝ (fun y => χ y*Real.exp (-F y)) x v =
      Real.exp (-F x)*(fderiv ℝ χ x v-χ x*fderiv ℝ F x v) := by
  have hc := (hχ.differentiable (by simp) x).hasFDerivAt
  have hf := (hF.differentiable (by simp) x).hasFDerivAt
  have he := ((Real.hasDerivAt_exp (-F x)).hasFDerivAt).comp x hf.neg
  have h := hc.mul he
  change HasFDerivAt (fun y => χ y*Real.exp (-F y)) _ x at h
  rw [h.fderiv]
  simp
  ring

theorem smooth_localized_exp_mixed {N : ℕ} {χ F : Configuration N → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hF : ContDiff ℝ ∞ F) (x v w : Configuration N) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => χ z*Real.exp (-F z)) y v) x w =
      Real.exp (-F x)*(fderiv ℝ (fun y => fderiv ℝ χ y v) x w-
        fderiv ℝ χ x v*fderiv ℝ F x w-fderiv ℝ χ x w*fderiv ℝ F x v+
        χ x*(fderiv ℝ F x v*fderiv ℝ F x w-
          fderiv ℝ (fun y => fderiv ℝ F y v) x w)) := by
  simp_rw [smooth_localized_exp_partial hχ hF]
  have hc := (hχ.differentiable (by simp) x).hasFDerivAt
  have hf := (hF.differentiable (by simp) x).hasFDerivAt
  have hdc : ContDiff ℝ ∞ (fun y => fderiv ℝ χ y v) :=
    (hχ.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  have hdf : ContDiff ℝ ∞ (fun y => fderiv ℝ F y v) :=
    (hF.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  have he := ((Real.hasDerivAt_exp (-F x)).hasFDerivAt).comp x hf.neg
  have hb := ((hdc.differentiable (by simp) x).hasFDerivAt).sub
    (hc.mul ((hdf.differentiable (by simp) x).hasFDerivAt))
  have h := he.mul hb
  change HasFDerivAt (fun y => Real.exp (-F y)*(fderiv ℝ χ y v-χ y*fderiv ℝ F y v)) _ x at h
  rw [h.fderiv]
  simp
  ring

#print axioms smooth_localized_exp_mixed
end TheoremT.Continuum
