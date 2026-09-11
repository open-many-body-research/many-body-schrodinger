import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

noncomputable section
namespace TheoremT.Continuum

theorem second_directional_composition {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {φ : F → G} {θ : E → F} (hφ : ContDiff ℝ 2 φ) (hθ : ContDiff ℝ 2 θ)
    (x v w : E) :
    fderiv ℝ (fun y => fderiv ℝ (φ ∘ θ) y v) x w =
      fderiv ℝ φ (θ x) (fderiv ℝ (fun y => fderiv ℝ θ y v) x w)+
      fderiv ℝ (fun z => fderiv ℝ φ z) (θ x) (fderiv ℝ θ x w) (fderiv ℝ θ x v) := by
  have hφ₁ : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hθ₁ : Differentiable ℝ θ := hθ.differentiable (by norm_num)
  have hφ₂ : Differentiable ℝ (fun z => fderiv ℝ φ z) :=
    (show ContDiff ℝ 1 (fun z => fderiv ℝ φ z) from hφ.fderiv_right (by norm_num)).differentiable (by norm_num)
  have hθ₂ : Differentiable ℝ (fun y => fderiv ℝ θ y) :=
    (show ContDiff ℝ 1 (fun y => fderiv ℝ θ y) from hθ.fderiv_right (by norm_num)).differentiable (by norm_num)
  have he : (fun y => fderiv ℝ (φ ∘ θ) y v)=
      (fun y => fderiv ℝ φ (θ y) (fderiv ℝ θ y v)) := by
    funext y
    rw [fderiv_comp y (hφ₁ (θ y)) (hθ₁ y)]
    rfl
  have hcd : DifferentiableAt ℝ (fun y => fderiv ℝ φ (θ y)) x :=
    (hφ₂ (θ x)).comp x (hθ₁ x)
  have hud : DifferentiableAt ℝ (fun y => fderiv ℝ θ y v) x :=
    (hθ₂ x).clm_apply (differentiableAt_const v)
  rw [he,fderiv_clm_apply hcd hud]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply]
  have hc : fderiv ℝ (fun y => fderiv ℝ φ (θ y)) x =
      (fderiv ℝ (fun z => fderiv ℝ φ z) (θ x)).comp (fderiv ℝ θ x) :=
    fderiv_comp x (hφ₂ (θ x)) (hθ₁ x)
  rw [hc]
  rfl

#print axioms second_directional_composition
end TheoremT.Continuum
