import GrushinWordSplitCoordinateCount_v1
import Mathlib.Data.Nat.Choose.Cast

/-! The actual ordered split list counts each choice, including repeated
letters. Its singleton and equal-pair coefficient counts are n and choose n 2.
The weighted summation lemma below keeps this list multiplicity exactly. -/
noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {ι : Type} [DecidableEq ι]

def wordSplitLeftCount (w a : List ι) : ℕ :=
  (spectatorWordSplits w).countP (fun ab => decide (ab.1 = a))

theorem wordSplitLeftCount_empty (w : List ι) : wordSplitLeftCount w [] = 1 := by
  induction w with
  | nil => simp [wordSplitLeftCount, spectatorWordSplits]
  | cons x w ih =>
    simpa [wordSplitLeftCount, spectatorWordSplits, List.countP_append,
      List.countP_map, Function.comp_def] using ih

theorem wordSplitLeftCount_cons_cons (w a : List ι) (x y : ι) :
    wordSplitLeftCount (y :: w) (x :: a) =
      (if y = x then wordSplitLeftCount w a else 0) + wordSplitLeftCount w (x :: a) := by
  by_cases h : y = x
  · subst y
    simp [wordSplitLeftCount, spectatorWordSplits, List.countP_append,
      List.countP_map, Function.comp_def]
  · simp [wordSplitLeftCount, spectatorWordSplits, List.countP_append,
      List.countP_map, Function.comp_def, h]

theorem wordSplitLeftCount_singleton (w : List ι) (x : ι) :
    wordSplitLeftCount w [x] = w.countP (fun y => decide (y = x)) := by
  induction w with
  | nil => simp [wordSplitLeftCount, spectatorWordSplits]
  | cons y w ih =>
    rw [wordSplitLeftCount_cons_cons, wordSplitLeftCount_empty, ih, List.countP_cons]
    by_cases h : y = x <;> simp [h, Nat.add_comm]

theorem wordSplitLeftCount_pair (w : List ι) (x : ι) :
    wordSplitLeftCount w [x,x] = (w.countP (fun y => decide (y = x))).choose 2 := by
  induction w with
  | nil => simp [wordSplitLeftCount, spectatorWordSplits]
  | cons y w ih =>
    rw [wordSplitLeftCount_cons_cons, wordSplitLeftCount_singleton, ih, List.countP_cons]
    by_cases h : y = x
    · simp only [h, decide_true, ite_true]
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
    · simp [h]

theorem list_sum_indicator_const {A : Type*} [AddCommMonoid A]
    {J : Type*} (l : List J) (P : J → Prop) [DecidablePred P] (v : A) :
    (l.map (fun a => if P a then v else 0)).sum =
      (l.countP (fun a => decide (P a))) • v := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.countP_cons, ih]
    by_cases h : P a <;> simp [h, add_nsmul, add_comm]

theorem wordSplit_sum_indicator_const {A : Type*} [AddCommMonoid A]
    (w a : List ι) (v : A) :
    ((spectatorWordSplits w).map (fun ab => if ab.1 = a then v else 0)).sum =
      wordSplitLeftCount w a • v :=
  list_sum_indicator_const (spectatorWordSplits w) (fun ab => ab.1 = a) v

end TheoremT.Continuum.WeakGrushin
