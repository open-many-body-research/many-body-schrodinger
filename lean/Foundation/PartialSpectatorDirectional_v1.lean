import CompactPartialIntegralSupport_v1

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum
variable {Y T F : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup T] [NormedSpace ℝ T]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def partialTDirectional (G : Y × T → F) (v : T) (p : Y × T) : F :=
  fderiv ℝ G p (0,v)

theorem partialTDirectional_contDiff {G : Y × T → F} (hG : ContDiff ℝ ∞ G) (v : T) :
    ContDiff ℝ ∞ (partialTDirectional G v) :=
  (hG.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const

theorem partialTDirectional_hasCompactSupport {G : Y × T → F}
    (hc : HasCompactSupport G) (v : T) : HasCompactSupport (partialTDirectional G v) :=
  hc.fderiv_apply ℝ (0,v)

theorem partialTDirectional_eq_slice {G : Y × T → F} (hG : ContDiff ℝ ∞ G)
    (y : Y) (t v : T) : fderiv ℝ (fun s => G (y,s)) t v = partialTDirectional G v (y,t) := by
  have hp : HasFDerivAt (fun s : T => (y,s)) (ContinuousLinearMap.inr ℝ Y T) t := by
    have he : (0 : T →L[ℝ] Y).prod (ContinuousLinearMap.id ℝ T) =
        ContinuousLinearMap.inr ℝ Y T := by ext x <;> rfl
    rw [← he]
    exact (hasFDerivAt_const y t).prodMk (hasFDerivAt_id t)
  exact congrArg (fun L : T →L[ℝ] F => L v)
    (((hG.differentiable (by simp) (y,t)).hasFDerivAt).comp t hp).fderiv

#print axioms partialTDirectional_contDiff
#print axioms partialTDirectional_hasCompactSupport
#print axioms partialTDirectional_eq_slice
end TheoremT.Continuum
