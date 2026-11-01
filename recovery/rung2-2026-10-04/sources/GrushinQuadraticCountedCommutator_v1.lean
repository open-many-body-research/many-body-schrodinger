import GrushinQuadraticCoordinateWord_v1
import CoordinateWordSplitCountedValues_v1
import ProductDirectionalWordCommutator_v1

/-! Exact quadratic proper ordered Leibniz sum on the counted natural family.
Every nonempty coefficient choice is grouped by its one or two equal Y hits.
The list retains multiplicity, yielding n and n(n-1) with no norm estimate. -/
noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum.WeakGrushin

theorem list_sum_finset_sum {A J I : Type*} [AddCommMonoid A]
    (l : List J) (s : Finset I) (f : J → I → A) :
    (l.map (fun a => ∑ i ∈ s, f a i)).sum =
      ∑ i ∈ s, (l.map (fun a => f a i)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Finset.sum_add_distrib]

theorem real_two_mul_choose_two (n : ℕ) :
    (2 : ℝ) * (n.choose 2 : ℝ) = ((n * (n-1) : ℕ) : ℝ) := by
  rw [Nat.cast_choose_two]
  cases n with
  | zero => norm_num
  | succ k => simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, Nat.cast_mul, Nat.cast_add, Nat.cast_one]; ring

theorem grushin_quadratic_counted_commutator
    (F : (Fin 4 → ℕ) → (Fin 3 → ℕ) → Space (Fin 3) → ℂ)
    (w : List (Fin 4 ⊕ Fin 3)) (p : Space (Fin 3)) :
    directionalWordCommutator productCoordinateDirection (fun q : Space (Fin 3) => ‖q.1‖^2)
      (mixedMultiIndexWordFamily F) w p =
      (2 : ℝ) • (∑ i : Fin 4, (factorialWordYCount w i : ℝ) • (p.1 i •
        F (factorialWordYCount w - Pi.single i 1) (factorialWordTCount w) p)) +
      ∑ i : Fin 4, ((factorialWordYCount w i * (factorialWordYCount w i-1) : ℕ) : ℝ) •
        F (factorialWordYCount w - Pi.single i 2) (factorialWordTCount w) p := by
  let L := spectatorWordProperSplits w
  let A := fun (ab : List (Fin 4 ⊕ Fin 3) × List (Fin 4 ⊕ Fin 3)) (i : Fin 4) =>
    if ab.1 = [Sum.inl i] then (2 * p.1 i) • mixedMultiIndexWordFamily F ab.2 p else 0
  let C := fun (ab : List (Fin 4 ⊕ Fin 3) × List (Fin 4 ⊕ Fin 3)) (i : Fin 4) =>
    if ab.1 = [Sum.inl i,Sum.inl i] then (2 : ℝ) • mixedMultiIndexWordFamily F ab.2 p else 0
  have hterm (ab : List (Fin 4 ⊕ Fin 3) × List (Fin 4 ⊕ Fin 3)) (hab : ab ∈ L) :
      directionalWordDeriv productCoordinateDirection (fun q : Space (Fin 3) => ‖q.1‖^2) ab.1 p •
        mixedMultiIndexWordFamily F ab.2 p = (∑ i, A ab i) + ∑ i, C ab i := by
    have hn := (spectatorWordProperSplits_strict hab).1
    have hne : ab.1 ≠ [] := by intro h; simp [h] at hn
    rw [grushin_quadratic_coordinate_word_nonempty ab.1 hne p, add_smul,
      Finset.sum_smul, Finset.sum_smul]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      by_cases h : ab.1 = [Sum.inl i] <;> simp [A,h]
    · apply Finset.sum_congr rfl
      intro i _
      by_cases h : ab.1 = [Sum.inl i,Sum.inl i] <;> simp [C,h]
  have hs : directionalWordCommutator productCoordinateDirection
      (fun q : Space (Fin 3) => ‖q.1‖^2) (mixedMultiIndexWordFamily F) w p =
      (∑ i : Fin 4, (L.map (fun ab => A ab i)).sum) +
      ∑ i : Fin 4, (L.map (fun ab => C ab i)).sum := by
    calc
      _ = (L.map (fun ab => (∑ i, A ab i) + ∑ i, C ab i)).sum := by
        apply congrArg List.sum
        exact List.map_congr_left hterm
      _ = _ := by
        rw [List.sum_map_add]
        exact congrArg₂ (fun x y : ℂ => x+y)
          (list_sum_finset_sum L Finset.univ A) (list_sum_finset_sum L Finset.univ C)
  have hA (i : Fin 4) : (L.map (fun ab => A ab i)).sum =
      (2 : ℝ) • ((factorialWordYCount w i : ℝ) • (p.1 i •
        F (factorialWordYCount w - Pi.single i 1) (factorialWordTCount w) p)) := by
    have h := wordProperSplit_counted_singleton
      (fun α β q => (2*p.1 i) • F α β q) w i p
    change (L.map (fun ab => A ab i)).sum = _ at h
    rw [h, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, smul_smul, smul_smul]
    congr 1
    ring
  have hC (i : Fin 4) : (L.map (fun ab => C ab i)).sum =
      ((factorialWordYCount w i * (factorialWordYCount w i-1) : ℕ) : ℝ) •
        F (factorialWordYCount w - Pi.single i 2) (factorialWordTCount w) p := by
    have h := wordProperSplit_counted_pair (fun α β q => (2 : ℝ) • F α β q) w i p
    change (L.map (fun ab => C ab i)).sum = _ at h
    rw [h, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_comm,
      real_two_mul_choose_two]
  rw [hs]
  simp_rw [hA,hC]
  rw [Finset.smul_sum]

end TheoremT.Continuum.WeakGrushin
