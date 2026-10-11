import ProductCoordinateWeakWordPermutation_v1
import LocalProductDirectionalWeakLinear_v1

/-! The appended spectator trace of an actual finite coordinate derivative
family. Appending two spectator labels preserves every outer coordinate
chain literally. The same-second spectator identity for each word follows
from proved weak permutation on the open domain, not a compatibility premise.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

def coordinateWordSpectatorTrace
    (D : List (Fin 4 ⊕ κ) → Space κ → ℂ) (w : List (Fin 4 ⊕ κ)) (p : Space κ) : ℂ :=
  ∑ j : κ, D (w ++ [Sum.inr j,Sum.inr j]) p

theorem coordinateWordSpectatorTrace_locallyL2
    {Ω : Set (Space κ)} {m : ℕ}
    (D : List (Fin 4 ⊕ κ) → Space κ → ℂ)
    (hD : ∀ w, w.length ≤ m+2 → ProductLocallyL2On (D w) Ω)
    (w : List (Fin 4 ⊕ κ)) (hw : w.length ≤ m) :
    ProductLocallyL2On (coordinateWordSpectatorTrace D w) Ω := by
  intro K hK hs
  apply memLp_finsetSum
  intro j hj
  exact (hD (w ++ [Sum.inr j,Sum.inr j]) (by
    simp only [List.length_append,List.length_cons,List.length_nil]
    omega)) K hK hs

theorem coordinateWordSpectatorTrace_localD
    {Ω : Set (Space κ)} {m : ℕ}
    (D : List (Fin 4 ⊕ κ) → Space κ → ℂ)
    (hD : ∀ w i, w.length < m+2 →
      ProductLocalWeakDirectional Ω (D w) (D (i :: w)) (productCoordinateDirection i))
    (w : List (Fin 4 ⊕ κ)) (i : Fin 4 ⊕ κ) (hw : w.length < m) :
    ProductLocalWeakDirectional Ω (coordinateWordSpectatorTrace D w)
      (coordinateWordSpectatorTrace D (i :: w)) (productCoordinateDirection i) := by
  have h := ProductLocalWeakDirectional.finset_sum Finset.univ
    (fun j : κ => D (w ++ [Sum.inr j,Sum.inr j]))
    (fun j : κ => D (i :: (w ++ [Sum.inr j,Sum.inr j])))
    (fun j _ => hD _ i (by simp only [List.length_append,List.length_cons,List.length_nil]; omega))
  change ProductLocalWeakDirectional Ω
    (fun p => ∑ j : κ, D (w ++ [Sum.inr j,Sum.inr j]) p)
    (fun p => ∑ j : κ, D ((i :: w) ++ [Sum.inr j,Sum.inr j]) p)
    (productCoordinateDirection i)
  simpa only [List.cons_append] using h

theorem coordinate_word_appended_second_spectator
    {Ω : Set (Space κ)} (hΩ : IsOpen Ω) {m : ℕ} {W : ℝ}
    (D : List (Fin 4 ⊕ κ) → Space κ → ℂ)
    (hBudget : ∀ w, w.length ≤ m+2 → RegionL2Budget (D w) Ω W)
    (hChain : ∀ w i, w.length < m+2 →
      ProductLocalWeakDirectional Ω (D w) (D (i :: w)) (productCoordinateDirection i))
    (w : List (Fin 4 ⊕ κ)) (hw : w.length ≤ m) (j : κ) :
    ProductLocalWeakDirectional Ω (D (Sum.inr j :: w))
      (D (w ++ [Sum.inr j,Sum.inr j])) (tDir j) := by
  apply product_coordinate_family_derivative_of_perm hΩ D hBudget hChain (Sum.inr j)
  · simpa only [List.cons_append,List.nil_append] using
      (List.perm_append_comm (l₁ := [Sum.inr j,Sum.inr j]) (l₂ := w))
  · simp only [List.length_cons]
    omega

#print axioms coordinateWordSpectatorTrace
#print axioms coordinateWordSpectatorTrace_locallyL2
#print axioms coordinateWordSpectatorTrace_localD
#print axioms coordinate_word_appended_second_spectator
end TheoremT.Continuum.WeakGrushin
