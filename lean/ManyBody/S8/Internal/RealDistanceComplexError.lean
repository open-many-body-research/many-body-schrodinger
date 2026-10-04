import ManyBody.S8.Internal.RealRationalAmbientProfile
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic
/-! Exact complexification of actual real distance-profile errors.
The genuine real-to-complex linear isometry preserves every iterated
Frechet operator norm. Actual first and second jet error bounds therefore
transport unchanged to the complex-valued physical profile, without any
weak-derivative or physical composition premise. -/
noncomputable section
set_option autoImplicit false
open Set Metric
open scoped Topology ContDiff
namespace ManyBody.S8

def realDistanceComplexError (g P : (Fin 3 → ℝ) → ℝ) (q : Fin 3 → ℝ) : ℂ :=
  ((g q-P q : ℝ) : ℂ)

theorem real_distance_complex_error_contDiffOn
    {g P : (Fin 3 → ℝ) → ℝ} {a : Fin 3 → ℝ} {R : ℝ}
    (hg : ContDiffOn ℝ ∞ g (ball a R)) (hP : ContDiff ℝ ∞ P) :
    ContDiffOn ℝ ∞ (realDistanceComplexError g P) (ball a R) := by
  exact Complex.ofRealCLM.contDiff.comp_contDiffOn (hg.sub hP.contDiffOn)

theorem real_distance_complex_error_iterated_norm
    {g P : (Fin 3 → ℝ) → ℝ} {q : Fin 3 → ℝ} {n : ℕ}
    (hg : ContDiffAt ℝ n g q) (hP : ContDiffAt ℝ n P q) :
    ‖iteratedFDeriv ℝ n (realDistanceComplexError g P) q‖=
      ‖iteratedFDeriv ℝ n g q-iteratedFDeriv ℝ n P q‖ := by
  change ‖iteratedFDeriv ℝ n (Complex.ofRealLI ∘ (fun x => g x-P x)) q‖=_
  rw [Complex.ofRealLI.norm_iteratedFDeriv_comp_left (hg.sub hP) le_rfl]
  change ‖iteratedFDeriv ℝ n (g-P) q‖=_
  rw [
    iteratedFDeriv_sub_apply hg hP]

theorem real_distance_complex_error_C2_bounds
    {g P : (Fin 3 → ℝ) → ℝ} {a q : Fin 3 → ℝ} {R ζ : ℝ}
    (hR : 0<R) (hg : ContDiffOn ℝ ∞ g (ball a R)) (hP : ContDiff ℝ ∞ P)
    (hq : q∈closedBall a (R/8))
    (hb : ∀k : Fin 3, ‖iteratedFDeriv ℝ (k:ℕ) g q-
      iteratedFDeriv ℝ (k:ℕ) P q‖≤ζ) :
    ‖realDistanceComplexError g P q‖≤ζ ∧
    ‖fderiv ℝ (realDistanceComplexError g P) q‖≤ζ ∧
    ‖fderiv ℝ (fderiv ℝ (realDistanceComplexError g P)) q‖≤ζ := by
  have hqb : q∈ball a R := by
    rw [mem_ball]
    have hh := hq
    rw [mem_closedBall] at hh
    linarith
  have hgq : ContDiffAt ℝ ∞ g q := hg.contDiffAt (isOpen_ball.mem_nhds hqb)
  have heq (k : Fin 3) := real_distance_complex_error_iterated_norm
    (hgq.of_le (by simp : (k:ℕ∞ω)≤∞))
    (hP.contDiffAt.of_le (by simp : (k:ℕ∞ω)≤∞))
  have hh (k : Fin 3) : ‖iteratedFDeriv ℝ (k:ℕ) (realDistanceComplexError g P) q‖≤ζ :=
    (heq k).trans_le (hb k)
  refine ⟨?_,?_,?_⟩
  · simpa only [Fin.val_zero,norm_iteratedFDeriv_zero] using hh 0
  · simpa only [Fin.val_one,norm_iteratedFDeriv_one] using hh 1
  · rw [←norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv (n:=1)]
    exact hh 2

#print axioms real_distance_complex_error_contDiffOn
#print axioms real_distance_complex_error_iterated_norm
#print axioms real_distance_complex_error_C2_bounds
end ManyBody.S8