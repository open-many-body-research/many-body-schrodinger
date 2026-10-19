import LocalProductDirectionalWeakAlgebra_v1
import SpectatorIterationState_v1

/-! Canonical mixed finite weak derivative families. A Y word is applied
outside a spectator word. The missing spectator chains are derived by weak
commutation from genuine Y-prefix chains and the pure spectator chains.
All functions occurring in the conclusion retain actual local L2 membership.
-/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem mixed_word_spectator_compatibility
    {Ω : Set (Space κ)} {r m : ℕ}
    (F : List (Fin 4) → List κ → Space κ → ℂ)
    (hY : ∀ a b i, a.length < r → a.length + b.length < m →
      ProductLocalWeakDirectional Ω (F a b) (F (i :: a) b) (yDir i))
    (hT : ∀ b j, b.length < m →
      ProductLocalWeakDirectional Ω (F [] b) (F [] (j :: b)) (tDir j))
    (a : List (Fin 4)) (b : List κ) (j : κ)
    (ha : a.length ≤ r) (hab : a.length + b.length < m) :
    ProductLocalWeakDirectional Ω (F a b) (F a (j :: b)) (tDir j) := by
  induction a with
  | nil => exact hT b j (by simpa using hab)
  | cons i a ih =>
    have har : a.length < r := by simp only [List.length_cons] at ha; omega
    have hab' : a.length + b.length < m := by
      simp only [List.length_cons] at hab; omega
    have hat : a.length + (j :: b).length < m := by
      simp only [List.length_cons] at hab ⊢; omega
    exact (ih (by omega) hab').swap (hY a b i har hab') (hY a (j :: b) i har hat)

theorem mixed_word_second_spectator_compatibility
    {Ω : Set (Space κ)} {r m : ℕ}
    (F : List (Fin 4) → List κ → Space κ → ℂ)
    (hY : ∀ a b i, a.length < r → a.length + b.length < m →
      ProductLocalWeakDirectional Ω (F a b) (F (i :: a) b) (yDir i))
    (hT : ∀ b j, b.length < m →
      ProductLocalWeakDirectional Ω (F [] b) (F [] (j :: b)) (tDir j))
    (a : List (Fin 4)) (b : List κ) (j k : κ)
    (ha : a.length ≤ r) (hab : a.length + b.length + 2 ≤ m) :
    ProductLocalWeakDirectional Ω (F a b) (F a (j :: b)) (tDir j) ∧
      ProductLocalWeakDirectional Ω (F a (j :: b)) (F a (k :: j :: b)) (tDir k) := by
  constructor
  · exact mixed_word_spectator_compatibility F hY hT a b j ha (by omega)
  · apply mixed_word_spectator_compatibility F hY hT a (j :: b) k ha
    simp only [List.length_cons]
    omega

#print axioms mixed_word_spectator_compatibility
#print axioms mixed_word_second_spectator_compatibility
end TheoremT.Continuum.WeakGrushin
