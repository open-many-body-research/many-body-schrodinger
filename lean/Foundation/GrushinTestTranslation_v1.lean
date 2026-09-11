import GrushinTestSupport_v1
import Mathlib.Analysis.Calculus.FDeriv.Add

noncomputable section
open scoped ContDiff BigOperators
namespace TheoremT.Continuum

theorem second_directional_comp_add_right
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (a w q : E) :
    fderiv ℝ (fun x => fderiv ℝ (fun p => f (p+a)) x w) q w =
      fderiv ℝ (fun x => fderiv ℝ f x w) (q+a) w := by
  simp_rw [fderiv_comp_add_right]
  exact congrArg (fun L : E →L[ℝ] F => L w)
    (fderiv_comp_add_right (𝕜 := ℝ) (f := fun x => fderiv ℝ f x w) (x := q) a)

variable {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T]
variable {ι : Type*} [Fintype ι]

theorem splitGrushin_spectator_translate (c : ℝ) (v : ι → T)
    (φ : KSSpace × T → ℝ) (s : T) (q : KSSpace × T) :
    splitGrushin c v (fun _ => 0) (fun p => φ (p+(0,s))) q =
      splitGrushin c v (fun _ => 0) φ (q+(0,s)) := by
  unfold splitGrushin
  simp only [second_directional_comp_add_right,Prod.fst_add,add_zero]

theorem spectator_translated_test_contDiff {φ : KSSpace × T → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (s : T) :
    ContDiff ℝ ∞ (fun p => φ (p+(0,s))) :=
  hφ.comp (contDiff_id.add contDiff_const)

theorem spectator_translated_test_hasCompactSupport {φ : KSSpace × T → ℝ}
    (hc : HasCompactSupport φ) (s : T) :
    HasCompactSupport (fun p => φ (p+(0,s))) :=
  hc.comp_homeomorph (Homeomorph.addRight (0,s))

#print axioms second_directional_comp_add_right
#print axioms splitGrushin_spectator_translate
#print axioms spectator_translated_test_contDiff
#print axioms spectator_translated_test_hasCompactSupport
end TheoremT.Continuum
