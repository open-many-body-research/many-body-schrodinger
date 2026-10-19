import CoordinateMultiIndexWord_v1
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Group.Pi.Lemmas

/-! Canonical seven-coordinate words for a pair of Y/T multiindices.
The canonical order is inherited unchanged from coordinateMultiIndexWord.
Adding one coordinate changes the word by a permutation of a prefixed word.
These are combinatorial identities and assert no derivative existence. -/
noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum

def mixedMultiIndex (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) (j : Fin 7) : ℕ :=
  Sum.elim α β (sevenCoordinateEquiv j)

def mixedMultiIndexWord (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) : List (Fin 4 ⊕ Fin 3) :=
  coordinateMultiIndexWord (mixedMultiIndex α β)

theorem mixedMultiIndex_sum (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) :
    (∑ j, mixedMultiIndex α β j) = (∑ i, α i) + ∑ j, β j := by
  exact (sevenCoordinateEquiv.sum_comp (Sum.elim α β)).trans (Fintype.sum_sumElim α β)

theorem mixedMultiIndexWord_length (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) :
    (mixedMultiIndexWord α β).length = (∑ i, α i) + ∑ j, β j := by
  rw [mixedMultiIndexWord, coordinateMultiIndexWord_length, mixedMultiIndex_sum]

theorem mixedMultiIndexWord_count_y (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) (i : Fin 4) :
    coordinateWordCount (Sum.inl i) (mixedMultiIndexWord α β) = α i := by
  rw [mixedMultiIndexWord, coordinateMultiIndexWord_count_y]
  simp only [mixedMultiIndex, sevenCoordinateEquiv,
    finSumFinEquiv_symm_apply_castAdd (n := 3), Sum.elim_inl]

theorem mixedMultiIndexWord_count_t (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) (j : Fin 3) :
    coordinateWordCount (Sum.inr j) (mixedMultiIndexWord α β) = β j := by
  rw [mixedMultiIndexWord, coordinateMultiIndexWord_count_t]
  simp only [mixedMultiIndex, sevenCoordinateEquiv,
    finSumFinEquiv_symm_apply_natAdd (m := 4), Sum.elim_inr]

theorem coordinateWordCount_cons (x y : Fin 4 ⊕ Fin 3) (w : List (Fin 4 ⊕ Fin 3)) :
    coordinateWordCount x (y :: w) = coordinateWordCount x w + if y = x then 1 else 0 := by
  simp [coordinateWordCount, List.countP_cons]

theorem coordinateMultiIndexWord_add_single_perm (γ : Fin 7 → ℕ) (j : Fin 7) :
    (coordinateMultiIndexWord (γ + Pi.single j 1)).Perm
      (sevenCoordinateEquiv j :: coordinateMultiIndexWord γ) := by
  letI : BEq (Fin 4 ⊕ Fin 3) := ⟨fun x y => decide (x = y)⟩
  let : LawfulBEq (Fin 4 ⊕ Fin 3) := by infer_instance
  apply List.perm_iff_count.mpr
  intro x
  obtain ⟨k, rfl⟩ := sevenCoordinateEquiv.surjective x
  have hc : coordinateWordCount (sevenCoordinateEquiv k)
      (coordinateMultiIndexWord (γ + Pi.single j 1)) =
      coordinateWordCount (sevenCoordinateEquiv k)
        (sevenCoordinateEquiv j :: coordinateMultiIndexWord γ) := by
    rw [coordinateMultiIndexWord_count, coordinateWordCount_cons, coordinateMultiIndexWord_count]
    by_cases hjk : j = k
    · subst j
      simp
    · have hne : sevenCoordinateEquiv j ≠ sevenCoordinateEquiv k :=
        sevenCoordinateEquiv.injective.ne hjk
      simp [Pi.add_apply, hjk, hne]
  simpa only [List.count_eq_countP, Bool.beq_eq_decide_eq, coordinateWordCount] using hc

theorem mixedMultiIndexWord_add_single_y_perm
    (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) (i : Fin 4) :
    (mixedMultiIndexWord (α + Pi.single i 1) β).Perm (Sum.inl i :: mixedMultiIndexWord α β) := by
  letI : BEq (Fin 4 ⊕ Fin 3) := ⟨fun x y => decide (x = y)⟩
  let : LawfulBEq (Fin 4 ⊕ Fin 3) := by infer_instance
  apply List.perm_iff_count.mpr
  intro x
  have hc : coordinateWordCount x (mixedMultiIndexWord (α + Pi.single i 1) β) =
      coordinateWordCount x (Sum.inl i :: mixedMultiIndexWord α β) := by
    cases x with
    | inl k =>
      rw [mixedMultiIndexWord_count_y, coordinateWordCount_cons, mixedMultiIndexWord_count_y]
      by_cases hik : i = k <;> simp [Pi.add_apply, hik]
    | inr j =>
      rw [mixedMultiIndexWord_count_t, coordinateWordCount_cons, mixedMultiIndexWord_count_t]
      simp
  simpa only [List.count_eq_countP, Bool.beq_eq_decide_eq, coordinateWordCount] using hc

theorem mixedMultiIndexWord_add_single_t_perm
    (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) (j : Fin 3) :
    (mixedMultiIndexWord α (β + Pi.single j 1)).Perm (Sum.inr j :: mixedMultiIndexWord α β) := by
  letI : BEq (Fin 4 ⊕ Fin 3) := ⟨fun x y => decide (x = y)⟩
  let : LawfulBEq (Fin 4 ⊕ Fin 3) := by infer_instance
  apply List.perm_iff_count.mpr
  intro x
  have hc : coordinateWordCount x (mixedMultiIndexWord α (β + Pi.single j 1)) =
      coordinateWordCount x (Sum.inr j :: mixedMultiIndexWord α β) := by
    cases x with
    | inl i =>
      rw [mixedMultiIndexWord_count_y, coordinateWordCount_cons, mixedMultiIndexWord_count_y]
      simp
    | inr k =>
      rw [mixedMultiIndexWord_count_t, coordinateWordCount_cons, mixedMultiIndexWord_count_t]
      by_cases hjk : j = k <;> simp [Pi.add_apply, hjk]
  simpa only [List.count_eq_countP, Bool.beq_eq_decide_eq, coordinateWordCount] using hc

theorem mixedMultiIndexWord_zero : mixedMultiIndexWord (fun _ => 0) (fun _ => 0) = [] := by
  apply List.eq_nil_of_length_eq_zero
  rw [mixedMultiIndexWord_length]
  simp

end TheoremT.Continuum
