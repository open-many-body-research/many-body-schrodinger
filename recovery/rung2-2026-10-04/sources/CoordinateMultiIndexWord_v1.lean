import H12MultiIndexCount_v2
import Mathlib.Logic.Equiv.Fin.Basic

/-! Canonical coordinate words for the seven-dimensional multiindices.
The first four coordinates are the Y directions; the last three are spectator
directions. This file asserts indexing facts, not derivative existence.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace TheoremT.Continuum

def sevenCoordinateEquiv : Fin 7 ≃ (Fin 4 ⊕ Fin 3) :=
  (finSumFinEquiv : Fin 4 ⊕ Fin 3 ≃ Fin 7).symm

def coordinateMultiIndexWord (alpha : Fin 7 → ℕ) : List (Fin 4 ⊕ Fin 3) :=
  (List.ofFn (fun i : Fin 7 => List.replicate (alpha i) (sevenCoordinateEquiv i))).flatten

def coordinateWordCount (j : Fin 4 ⊕ Fin 3) (w : List (Fin 4 ⊕ Fin 3)) : ℕ :=
  w.countP (fun i => decide (i = j))

theorem coordinateMultiIndexWord_length (alpha : Fin 7 → ℕ) :
    (coordinateMultiIndexWord alpha).length = ∑ i, alpha i := by
  simp only [coordinateMultiIndexWord, List.length_flatten, List.map_ofFn,
    Function.comp_apply, List.length_replicate, List.sum_ofFn]

theorem coordinateMultiIndexWord_count (alpha : Fin 7 → ℕ) (j : Fin 7) :
    coordinateWordCount (sevenCoordinateEquiv j) (coordinateMultiIndexWord alpha) = alpha j := by
  simp only [coordinateWordCount, coordinateMultiIndexWord, List.countP_flatten, List.map_ofFn,
    Function.comp_apply, List.sum_ofFn]
  have hterm (i : Fin 7) :
      (List.replicate (alpha i) (sevenCoordinateEquiv i)).countP
          (fun a => decide (a = sevenCoordinateEquiv j)) =
        if i = j then alpha i else 0 := by
    by_cases hij : i = j
    · subst i; simp only [List.countP_replicate, decide_true, ite_true]
    · have he : sevenCoordinateEquiv i ≠ sevenCoordinateEquiv j :=
        sevenCoordinateEquiv.injective.ne hij
      rw [List.countP_replicate]
      simp [hij, he]
  simp_rw [hterm]
  simp

theorem coordinateMultiIndexWord_count_y (alpha : Fin 7 → ℕ) (i : Fin 4) :
    coordinateWordCount (Sum.inl i) (coordinateMultiIndexWord alpha) = alpha (Fin.castAdd 3 i) := by
  simpa only [sevenCoordinateEquiv, finSumFinEquiv_symm_apply_castAdd (n := 3)] using
    coordinateMultiIndexWord_count alpha (Fin.castAdd 3 i)

theorem coordinateMultiIndexWord_count_t (alpha : Fin 7 → ℕ) (j : Fin 3) :
    coordinateWordCount (Sum.inr j) (coordinateMultiIndexWord alpha) = alpha (Fin.natAdd 4 j) := by
  simpa only [sevenCoordinateEquiv, finSumFinEquiv_symm_apply_natAdd (m := 4)] using
    coordinateMultiIndexWord_count alpha (Fin.natAdd 4 j)

theorem coordinateMultiIndexWord_injective : Function.Injective coordinateMultiIndexWord := by
  intro alpha beta h
  funext i
  have hc := congrArg (coordinateWordCount (sevenCoordinateEquiv i)) h
  simpa only [coordinateMultiIndexWord_count] using hc

def h12CoordinateWord (alpha : boundedMultiIndex 7 12) : List (Fin 4 ⊕ Fin 3) :=
  coordinateMultiIndexWord alpha.val

def h12ZeroMultiIndex : boundedMultiIndex 7 12 := ⟨fun _ => 0, by simp⟩

theorem h12CoordinateWord_length (alpha : boundedMultiIndex 7 12) :
    (h12CoordinateWord alpha).length = ∑ i, alpha.val i :=
  coordinateMultiIndexWord_length alpha.val

theorem h12CoordinateWord_length_le (alpha : boundedMultiIndex 7 12) :
    (h12CoordinateWord alpha).length ≤ 12 := by
  rw [h12CoordinateWord_length]
  exact alpha.property

theorem h12CoordinateWord_zero : h12CoordinateWord h12ZeroMultiIndex = [] := by
  apply List.eq_nil_of_length_eq_zero
  rw [h12CoordinateWord_length]
  simp [h12ZeroMultiIndex]

theorem h12CoordinateWord_injective : Function.Injective h12CoordinateWord := by
  intro alpha beta h
  apply Subtype.ext
  exact coordinateMultiIndexWord_injective h

end TheoremT.Continuum
