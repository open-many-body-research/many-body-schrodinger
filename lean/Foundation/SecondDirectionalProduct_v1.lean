import SecondDirectionalComposition_v1
import Mathlib.Analysis.Calculus.FDeriv.Mul

noncomputable section
open scoped ContDiff
namespace TheoremT.Continuum

theorem first_directional_product {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (x v : E) :
    fderiv ℝ (fun y => f y*g y) x v =
      fderiv ℝ f x v*g x+f x*fderiv ℝ g x v := by
  have hh := (hf x).hasFDerivAt.mul (hg x).hasFDerivAt
  change HasFDerivAt (fun y => f y*g y) _ x at hh
  rw [hh.fderiv]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
  ring

theorem second_directional_product {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x v w : E) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => f z*g z) y v) x w =
      fderiv ℝ (fun y => fderiv ℝ f y v) x w*g x+
      fderiv ℝ f x v*fderiv ℝ g x w+
      fderiv ℝ f x w*fderiv ℝ g x v+
      f x*fderiv ℝ (fun y => fderiv ℝ g y v) x w := by
  have hf' := hf.differentiable (by simp)
  have hg' := hg.differentiable (by simp)
  have hdf : Differentiable ℝ (fun y => fderiv ℝ f y v) :=
    ((hf.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const).differentiable (by simp)
  have hdg : Differentiable ℝ (fun y => fderiv ℝ g y v) :=
    ((hg.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const).differentiable (by simp)
  have he : (fun y => fderiv ℝ (fun z => f z*g z) y v) =
    (fun y => fderiv ℝ f y v*g y+f y*fderiv ℝ g y v) := by
    funext y
    exact first_directional_product hf' hg' y v
  have hh := ((hdf x).hasFDerivAt.mul (hg' x).hasFDerivAt).add
    ((hf' x).hasFDerivAt.mul (hdg x).hasFDerivAt)
  change HasFDerivAt (fun y => fderiv ℝ f y v*g y+f y*fderiv ℝ g y v) _ x at hh
  rw [he,hh.fderiv]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
  ring

#print axioms second_directional_product
end TheoremT.Continuum
