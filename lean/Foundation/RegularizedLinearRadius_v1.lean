import ConfigurationRadiusWeakGradient_v1
import ConfigurationSlicing_v2

/-! Actual regularized physical distance after a real continuous linear map.
This handles electron positions and unnormalized pair differences. -/
noncomputable section
open scoped ContDiff
namespace TheoremT.Continuum

def regularizedLinearRadius {N : ℕ} (A : Configuration N →L[ℝ] Position)
    (δ : ℝ) (x : Configuration N) : ℝ := Real.sqrt (‖A x‖^2+δ)

theorem regularizedLinearRadius_pos {N : ℕ} (A : Configuration N →L[ℝ] Position)
    {δ : ℝ} (hδ : 0 < δ) (x : Configuration N) : 0 < regularizedLinearRadius A δ x :=
  Real.sqrt_pos.mpr (by positivity)

theorem regularizedLinearRadius_sq {N : ℕ} (A : Configuration N →L[ℝ] Position)
    {δ : ℝ} (hδ : 0 < δ) (x : Configuration N) :
    (regularizedLinearRadius A δ x)^2 = ‖A x‖^2+δ := Real.sq_sqrt (by positivity)

theorem regularizedLinearRadius_contDiff {N : ℕ} (A : Configuration N →L[ℝ] Position)
    {δ : ℝ} (hδ : 0 < δ) : ContDiff ℝ ∞ (regularizedLinearRadius A δ) :=
  (((contDiff_norm_sq ℝ).comp A.contDiff).add contDiff_const).sqrt (fun x => (show ‖A x‖^2+δ ≠ 0 by positivity))

theorem regularizedLinearRadius_fderiv_apply {N : ℕ} (A : Configuration N →L[ℝ] Position)
    {δ : ℝ} (hδ : 0 < δ) (x v : Configuration N) :
    fderiv ℝ (regularizedLinearRadius A δ) x v =
      inner ℝ (A x) (A v)/regularizedLinearRadius A δ x := by
  have hh := ((((hasStrictFDerivAt_norm_sq (A x)).hasFDerivAt.comp x A.hasFDerivAt).add_const δ).sqrt (by positivity : ‖A x‖^2+δ ≠ 0))
  change HasFDerivAt (regularizedLinearRadius A δ) _ x at hh
  rw [hh.fderiv]
  simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.add_apply,Function.comp_def,
    innerSL_apply_apply,smul_eq_mul,two_smul]
  unfold regularizedLinearRadius
  ring

theorem regularizedLinearRadius_mixed_partial {N : ℕ} (A : Configuration N →L[ℝ] Position)
    {δ : ℝ} (hδ : 0 < δ) (x v w : Configuration N) :
    fderiv ℝ (fun y => fderiv ℝ (regularizedLinearRadius A δ) y v) x w =
      inner ℝ (A w) (A v)/regularizedLinearRadius A δ x -
        (inner ℝ (A x) (A v)*inner ℝ (A x) (A w))/(regularizedLinearRadius A δ x)^3 := by
  have he : (fun y => fderiv ℝ (regularizedLinearRadius A δ) y v) =
      (fun y => inner ℝ (A y) (A v)*(regularizedLinearRadius A δ y)⁻¹) := by
    funext y; rw [regularizedLinearRadius_fderiv_apply A hδ,div_eq_mul_inv]
  rw [he]
  have hr := ((regularizedLinearRadius_contDiff A hδ).differentiable (by simp) x).hasFDerivAt
  have hn := (A.hasFDerivAt (x := x)).inner ℝ (hasFDerivAt_const (A v) x)
  have h := hn.mul ((hasFDerivAt_inv (regularizedLinearRadius_pos A hδ x).ne').comp x hr)
  change HasFDerivAt (fun y => inner ℝ (A y) (A v)*(regularizedLinearRadius A δ y)⁻¹) _ x at h
  rw [h.fderiv]
  simp [regularizedLinearRadius_fderiv_apply A hδ,real_inner_comm]
  ring

#print axioms regularizedLinearRadius_fderiv_apply
#print axioms regularizedLinearRadius_mixed_partial
end TheoremT.Continuum
