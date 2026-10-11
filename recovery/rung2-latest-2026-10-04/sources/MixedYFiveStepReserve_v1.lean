import MixedYFiniteIteration_v1

/-! The exact five Y stages needed after the twelve-stage spectator reserve.
The input contains no higher Y derivatives than the retained two levels.
Only mixed coefficient and source words through total order ten are used.
The endpoint has all actual mixed words through total order twelve. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem spectatorFiniteState_five_y_steps
    (c : ℝ) (Ω V : ℕ → Set (Space κ)) (χ η : ℕ → Space κ → ℝ)
    (M A L D Q : ℕ → ℝ)
    (hGeom : ∀ k, k < 5 → SpectatorStepGeometry 0 (Ω k) (Ω (k+1)) (V k)
      (χ k) (η k) (M k) (A k) (L k) (D k) (Q k))
    (hO : ∀ k, k < 5 → IsOpen (Ω (k+1)))
    {B : Space κ → ℝ} (hB : ContDiffOn ℝ ∞ B (Ω 0))
    (K0 Q0 H0 Winit : ℝ) (hWinit : 0 ≤ Winit)
    (f : Space κ → ℂ) (S : List (Fin 4) → List κ → Space κ → ℂ)
    (hf : SpectatorFiniteState (Ω 0) f 12 Winit)
    (hS : ∀ a b, a.length+b.length ≤ 10 → RegionL2Budget (S a b) (Ω 0) H0)
    (hSY : ∀ a b i, a.length+b.length < 10 →
      ProductLocalWeakDirectional (Ω 0) (S a b) (S (i :: a) b) (yDir i))
    (hST : ∀ b j, b.length < 10 →
      ProductLocalWeakDirectional (Ω 0) (S [] b) (S [] (j :: b)) (tDir j))
    (hCoeff : ∀ a b, a.length+b.length ≤ 10 → ∀ p ∈ Ω 0,
      |directionalWordDeriv yDir (spectatorWordDeriv B b) a p| ≤ K0)
    (hQuad : ∀ a, a.length ≤ 10 → ∀ p ∈ Ω 0,
      |directionalWordDeriv yDir (fun p : Space κ => ‖p.1‖^2) a p| ≤ Q0)
    (hP : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω 0 →
      (∫ p, splitGrushin c oscillatorBasis B φ p • f p) = ∫ p, φ p • S [] [] p) :
    0 ≤ mixedYIterationBudgetSeq c M A L D Q K0 Q0 H0 12 (Fintype.card κ) Winit 5 ∧
    MixedTriangularState (Ω 5) f 12 12
      (mixedYIterationBudgetSeq c M A L D Q K0 Q0 H0 12 (Fintype.card κ) Winit 5) := by
  have hh := mixedTriangularState_potential_iterate c 5 Ω V χ η M A L D Q hGeom hO hB
    (r := 2) (m := 12) (by norm_num) K0 Q0 H0 Winit hWinit f S
    (spectatorFiniteState_to_mixedTriangularState hf)
    (fun a b hab => hS a b (by omega))
    (fun a b i hab => hSY a b i (by omega))
    (fun b j hb => hST b j (by omega))
    (fun a b hab p hp => hCoeff a b (by omega) p hp)
    (fun a ha p hp => hQuad a (by omega) p hp) hP
  simpa only [show 2+2*5=12 by norm_num] using hh

#print axioms spectatorFiniteState_five_y_steps
end TheoremT.Continuum.WeakGrushin
