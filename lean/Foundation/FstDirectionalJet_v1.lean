import SecondDirectionalComposition_v1

noncomputable section
open scoped ContDiff
namespace TheoremT.Continuum

theorem first_directional_fst {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {h : E → ℝ}
    (hh : Differentiable ℝ h) (q v : E × F) :
    fderiv ℝ (fun x : E × F => h x.1) q v = fderiv ℝ h q.1 v.1 := by
  have hd := (hh q.1).hasFDerivAt.comp q hasFDerivAt_fst
  change HasFDerivAt (fun x : E × F => h x.1) _ q at hd
  rw [hd.fderiv]
  rfl

theorem second_directional_fst {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {h : E → ℝ}
    (hh : ContDiff ℝ ∞ h) (q v w : E × F) :
    fderiv ℝ (fun x : E × F => fderiv ℝ (fun y : E × F => h y.1) x v) q w =
      fderiv ℝ (fun x => fderiv ℝ h x v.1) q.1 w.1 := by
  have he : (fun x : E × F => fderiv ℝ (fun y : E × F => h y.1) x v) =
      (fun x : E × F => fderiv ℝ h x.1 v.1) := by
    funext x
    exact first_directional_fst (hh.differentiable (by simp)) x v
  rw [he]
  exact first_directional_fst
    (((hh.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const).differentiable (by simp)) q w

#print axioms second_directional_fst
end TheoremT.Continuum
