import CoordinateWordSplitSmallMultiplicity_v1
import ProductMixedMultiIndexWordFamily_v1

/-! Exact values of counted natural jets on a selected ordered split.
Count conservation identifies the remaining multiindex before multiplicities
are summed. Zero or insufficient coordinate counts use ordinary natural
subtraction and have zero selection multiplicity. -/
noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum.WeakGrushin

theorem factorialWordSplits_right_counts
    {w : List (Fin 4 ⊕ Fin 3)}
    {ab : List (Fin 4 ⊕ Fin 3) × List (Fin 4 ⊕ Fin 3)}
    (hab : ab ∈ spectatorWordSplits w) :
    factorialWordYCount ab.2 = factorialWordYCount w - factorialWordYCount ab.1 ∧
    factorialWordTCount ab.2 = factorialWordTCount w - factorialWordTCount ab.1 := by
  obtain ⟨hy,ht⟩ := factorialWordSplits_counts hab
  constructor
  · funext i
    have hi := hy i
    simp only [Pi.sub_apply]
    omega
  · funext j
    have hj := ht j
    simp only [Pi.sub_apply]
    omega

theorem wordSplit_sum_indicator_counted
    (F : (Fin 4 → ℕ) → (Fin 3 → ℕ) → Space (Fin 3) → ℂ)
    (w a : List (Fin 4 ⊕ Fin 3)) (p : Space (Fin 3)) :
    ((spectatorWordSplits w).map (fun ab =>
      if ab.1 = a then mixedMultiIndexWordFamily F ab.2 p else 0)).sum =
      wordSplitLeftCount w a • F (factorialWordYCount w - factorialWordYCount a)
        (factorialWordTCount w - factorialWordTCount a) p := by
  calc
    _ = ((spectatorWordSplits w).map (fun ab => if ab.1 = a then
        F (factorialWordYCount w - factorialWordYCount a)
          (factorialWordTCount w - factorialWordTCount a) p else 0)).sum := by
      congr 1
      apply List.map_congr_left
      intro ab hab
      by_cases ha : ab.1 = a
      · obtain ⟨hy,ht⟩ := factorialWordSplits_right_counts hab
        simp only [ha, ite_true, mixedMultiIndexWordFamily]
        rw [hy,ht,ha]
      · simp [ha]
    _ = _ := wordSplit_sum_indicator_const w a _

theorem wordProperSplit_sum_indicator_counted
    (F : (Fin 4 → ℕ) → (Fin 3 → ℕ) → Space (Fin 3) → ℂ)
    (w a : List (Fin 4 ⊕ Fin 3)) (ha : a ≠ []) (p : Space (Fin 3)) :
    ((spectatorWordProperSplits w).map (fun ab =>
      if ab.1 = a then mixedMultiIndexWordFamily F ab.2 p else 0)).sum =
      wordSplitLeftCount w a • F (factorialWordYCount w - factorialWordYCount a)
        (factorialWordTCount w - factorialWordTCount a) p := by
  have h := wordSplit_sum_indicator_counted F w a p
  rw [spectatorWordSplits_eq_proper_append] at h
  simpa [List.map_append, List.sum_append, Ne.symm ha] using h

theorem wordProperSplit_counted_singleton
    (F : (Fin 4 → ℕ) → (Fin 3 → ℕ) → Space (Fin 3) → ℂ)
    (w : List (Fin 4 ⊕ Fin 3)) (i : Fin 4) (p : Space (Fin 3)) :
    ((spectatorWordProperSplits w).map (fun ab =>
      if ab.1 = [Sum.inl i] then mixedMultiIndexWordFamily F ab.2 p else 0)).sum =
      factorialWordYCount w i • F (factorialWordYCount w - Pi.single i 1)
        (factorialWordTCount w) p := by
  have h := wordProperSplit_sum_indicator_counted F w [Sum.inl i] (by simp) p
  rw [wordSplitLeftCount_singleton] at h
  have ht0 : factorialWordTCount w - (0 : Fin 3 → ℕ) = factorialWordTCount w := by
    funext j
    simp
  simpa only [factorialWordYCount_cons_y, factorialWordTCount_cons_y,
    factorialWordYCount_nil, factorialWordTCount_nil, zero_add, ht0,
    factorialWordYCount, coordinateWordCount] using h

theorem wordProperSplit_counted_pair
    (F : (Fin 4 → ℕ) → (Fin 3 → ℕ) → Space (Fin 3) → ℂ)
    (w : List (Fin 4 ⊕ Fin 3)) (i : Fin 4) (p : Space (Fin 3)) :
    ((spectatorWordProperSplits w).map (fun ab =>
      if ab.1 = [Sum.inl i,Sum.inl i] then mixedMultiIndexWordFamily F ab.2 p else 0)).sum =
      (factorialWordYCount w i).choose 2 • F (factorialWordYCount w - Pi.single i 2)
        (factorialWordTCount w) p := by
  have hy : factorialWordYCount [Sum.inl i,Sum.inl i] = Pi.single i 2 := by
    funext k
    by_cases hik : i = k <;> simp [factorialWordYCount, coordinateWordCount, hik]
  have ht : factorialWordTCount [Sum.inl i,Sum.inl i] = 0 := by
    rw [factorialWordTCount_cons_y, factorialWordTCount_cons_y, factorialWordTCount_nil]
  have h := wordProperSplit_sum_indicator_counted F w [Sum.inl i,Sum.inl i] (by simp) p
  have ht0 : factorialWordTCount w - (0 : Fin 3 → ℕ) = factorialWordTCount w := by
    funext j
    simp
  rw [wordSplitLeftCount_pair,hy,ht,ht0] at h
  exact h

end TheoremT.Continuum.WeakGrushin
