import MixedTriangularState_v1
import LocalProductDirectionalWeakCompatibility_v1

/-! Extending a triangular weak derivative family by two Y levels. Only
second-jet gains at predecessor Y lengths r-1 and r, with total length at
most m-2, are used. Uniqueness identifies recovered first jets with the
previous family. Thus the odd-order boundary does not ask for m+1 total
orders. This algebraic step retains the actual gain premises explicitly.
-/
noncomputable section
open MeasureTheory
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

set_option maxHeartbeats 1200000 in
theorem mixed_triangular_extend_two
    {Ω : Set (Space κ)} (hΩ : IsOpen Ω) {r m : ℕ} (hr : 1 ≤ r) {W U : ℝ}
    (F : List (Fin 4) → List κ → Space κ → ℂ)
    (G : List (Fin 4) → List κ → Fin 4 → Space κ → ℂ)
    (E : List (Fin 4) → List κ → Fin 4 → Fin 4 → Space κ → ℂ)
    (hW : W ≤ U)
    (hF : ∀ a b, a.length ≤ r → a.length + b.length ≤ m → RegionL2Budget (F a b) Ω W)
    (hY : ∀ a b i, a.length < r → a.length + b.length < m →
      ProductLocalWeakDirectional Ω (F a b) (F (i :: a) b) (yDir i))
    (hT : ∀ b j, b.length < m →
      ProductLocalWeakDirectional Ω (F [] b) (F [] (j :: b)) (tDir j))
    (hgain : ∀ a b, a.length ≤ r → r ≤ a.length + 1 → a.length + b.length + 2 ≤ m →
      (∀ i, ProductLocalWeakDirectional Ω (F a b) (G a b i) (yDir i)) ∧
      (∀ i j, ProductLocalWeakDirectional Ω (G a b i) (E a b i j) (yDir j)) ∧
      ∀ i j, RegionL2Budget (E a b i j) Ω U) :
    MixedTriangularState Ω (F [] []) (r+2) m U := by
  let Fnext : List (Fin 4) → List κ → Space κ → ℂ := fun a b =>
    if a.length ≤ r then F a b else
      match a with
      | j :: i :: a => E a b i j
      | _ => fun _ => 0
  have hAttach (a : List (Fin 4)) (b : List κ) (i j : Fin 4)
      (ha : a.length < r) (hb : r ≤ a.length+1) (hab : a.length+b.length+2 ≤ m) :
      ProductLocalWeakDirectional Ω (F (i :: a) b) (E a b i j) (yDir j) := by
    have hg := hgain a b (by omega) hb hab
    exact (hY a b i ha (by omega)).second_of_compatible_first hΩ (hg.1 i) (hg.2.1 i j)
  have hFn (a : List (Fin 4)) (b : List κ) (ha : a.length ≤ r+2)
      (hab : a.length+b.length ≤ m) : RegionL2Budget (Fnext a b) Ω U := by
    by_cases hold : a.length ≤ r
    · simpa only [Fnext,if_pos hold] using (hF a b hold hab).restrict (Set.Subset.refl Ω) hW
    · cases a with
      | nil => simp at hold
      | cons j a =>
        cases a with
        | nil => simp only [List.length_cons,List.length_nil] at hold; omega
        | cons i a =>
          have hal : a.length ≤ r := by simp only [List.length_cons] at ha; omega
          have hbd : r ≤ a.length+1 := by simp only [List.length_cons] at hold; omega
          have hn : a.length+b.length+2 ≤ m := by simp only [List.length_cons] at hab; omega
          simpa only [Fnext,if_neg hold] using (hgain a b hal hbd hn).2.2 i j
  have hYn (a : List (Fin 4)) (b : List κ) (k : Fin 4)
      (ha : a.length < r+2) (hab : a.length+b.length < m) :
      ProductLocalWeakDirectional Ω (Fnext a b) (Fnext (k :: a) b) (yDir k) := by
    by_cases hold : a.length < r
    · have hs : a.length ≤ r := by omega
      have ht : (k :: a).length ≤ r := by simp only [List.length_cons]; omega
      simpa only [Fnext,if_pos hs,if_pos ht] using hY a b k hold hab
    · by_cases htop : a.length ≤ r
      · have hlen : a.length = r := by omega
        have ht : ¬ (k :: a).length ≤ r := by simp only [List.length_cons]; omega
        cases a with
        | nil => simp only [List.length_nil] at hlen; omega
        | cons i a =>
          have hal : a.length < r := by simp only [List.length_cons] at hlen; omega
          have hbd : r ≤ a.length+1 := by simp only [List.length_cons] at hlen; omega
          have hn : a.length+b.length+2 ≤ m := by simp only [List.length_cons] at hab; omega
          simpa only [Fnext,if_pos htop,if_neg ht] using hAttach a b i k hal hbd hn
      · have ht : ¬ (k :: a).length ≤ r := by simp only [List.length_cons]; omega
        have hlen : a.length = r+1 := by omega
        cases a with
        | nil => simp at htop
        | cons j a =>
          cases a with
          | nil => simp only [List.length_cons,List.length_nil] at hlen; omega
          | cons i a =>
            have hal : a.length < r := by simp only [List.length_cons] at hlen; omega
            have hbd : r ≤ a.length+1 := by simp only [List.length_cons] at hlen; omega
            have hn : a.length+b.length+2 ≤ m := by simp only [List.length_cons] at hab; omega
            have hial : (i :: a).length ≤ r := by simp only [List.length_cons] at hlen ⊢; omega
            have hibd : r ≤ (i :: a).length+1 := by simp only [List.length_cons] at hlen ⊢; omega
            have hin : (i :: a).length+b.length+2 ≤ m := by
              simp only [List.length_cons] at hab ⊢; omega
            have hg := hgain (i :: a) b hial hibd hin
            have he := (hAttach a b i j hal hbd hn).second_of_compatible_first hΩ
              (hg.1 j) (hg.2.1 j k)
            simpa only [Fnext,if_neg htop,if_neg ht] using he
  have hTn (b : List κ) (j : κ) (hb : b.length < m) :
      ProductLocalWeakDirectional Ω (Fnext [] b) (Fnext [] (j :: b)) (tDir j) := by
    simpa only [Fnext,List.length_nil,Nat.zero_le,if_true] using hT b j hb
  refine ⟨Fnext,?_,hFn,hYn,fun a b j ha hab =>
    mixed_word_spectator_compatibility Fnext hYn hTn a b j ha hab⟩
  simp only [Fnext,List.length_nil,Nat.zero_le,if_true]

#print axioms mixed_triangular_extend_two
end TheoremT.Continuum.WeakGrushin
