import SecondDirectionalComposition_v1
import Mathlib.Analysis.Calculus.FDeriv.Congr

noncomputable section
open Filter
open scoped Topology
namespace TheoremT.Continuum

theorem second_directional_composition_at {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {φ : F → G} {θ : E → F} (x v w : E)
    (hφ : ContDiffAt ℝ 2 φ (θ x)) (hθ : ContDiffAt ℝ 2 θ x) :
    fderiv ℝ (fun y => fderiv ℝ (φ ∘ θ) y v) x w =
      fderiv ℝ φ (θ x) (fderiv ℝ (fun y => fderiv ℝ θ y v) x w)+
      fderiv ℝ (fun z => fderiv ℝ φ z) (θ x) (fderiv ℝ θ x w) (fderiv ℝ θ x v) := by
  have hφ₁ := hφ.differentiableAt (by norm_num)
  have hθ₁ := hθ.differentiableAt (by norm_num)
  have hφ₂ : DifferentiableAt ℝ (fun z => fderiv ℝ φ z) (θ x) :=
    (show ContDiffAt ℝ 1 (fun z => fderiv ℝ φ z) (θ x) from hφ.fderiv_right (by norm_num)).differentiableAt (by norm_num)
  have hθ₂ : DifferentiableAt ℝ (fun y => fderiv ℝ θ y) x :=
    (show ContDiffAt ℝ 1 (fun y => fderiv ℝ θ y) x from hθ.fderiv_right (by norm_num)).differentiableAt (by norm_num)
  have he : (fun y => fderiv ℝ (φ ∘ θ) y v) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ φ (θ y) (fderiv ℝ θ y v)) := by
    filter_upwards [hθ.continuousAt (hφ.eventually (by norm_num)),hθ.eventually (by norm_num)] with y hy hz
    change ContDiffAt ℝ 2 φ (θ y) at hy
    rw [fderiv_comp y (hy.differentiableAt (by norm_num)) (hz.differentiableAt (by norm_num))]
    rfl
  have hcd : DifferentiableAt ℝ (fun y => fderiv ℝ φ (θ y)) x := hφ₂.comp x hθ₁
  have hud : DifferentiableAt ℝ (fun y => fderiv ℝ θ y v) x :=
    hθ₂.clm_apply (differentiableAt_const v)
  rw [he.fderiv_eq (𝕜 := ℝ),fderiv_clm_apply hcd hud]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply]
  have hc : fderiv ℝ (fun y => fderiv ℝ φ (θ y)) x =
      (fderiv ℝ (fun z => fderiv ℝ φ z) (θ x)).comp (fderiv ℝ θ x) :=
    fderiv_comp x hφ₂ hθ₁
  rw [hc]
  rfl

#print axioms second_directional_composition_at
end TheoremT.Continuum
