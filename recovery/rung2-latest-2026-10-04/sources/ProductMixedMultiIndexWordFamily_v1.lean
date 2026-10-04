import ProductMixedMultiIndexWeakHk_v1
import GrushinWordSplitCoordinateCount_v1

/-! Counted coordinate words for genuine finite natural multiindex jets.
The family below uses exactly the supplied natural-index representatives.
Counting turns each prefixed coordinate into its actual weak derivative,
with no representative replacement or additional regularity premise.
These finite identities assert no factorial estimate.
-/
noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum.WeakGrushin

theorem factorialWordYCount_nil : factorialWordYCount [] = 0 := by
  funext i
  simp [factorialWordYCount, coordinateWordCount]

theorem factorialWordTCount_nil : factorialWordTCount [] = 0 := by
  funext j
  simp [factorialWordTCount, coordinateWordCount]

theorem factorialWordYCount_cons_y (w : List (Fin 4 ⊕ Fin 3)) (i : Fin 4) :
    factorialWordYCount (Sum.inl i :: w) = factorialWordYCount w + Pi.single i 1 := by
  funext k
  rw [factorialWordYCount, coordinateWordCount_cons]
  by_cases hik : i = k <;> simp [factorialWordYCount, Pi.add_apply, hik]

theorem factorialWordTCount_cons_y (w : List (Fin 4 ⊕ Fin 3)) (i : Fin 4) :
    factorialWordTCount (Sum.inl i :: w) = factorialWordTCount w := by
  funext j
  simp [factorialWordTCount, coordinateWordCount_cons]

theorem factorialWordYCount_cons_t (w : List (Fin 4 ⊕ Fin 3)) (j : Fin 3) :
    factorialWordYCount (Sum.inr j :: w) = factorialWordYCount w := by
  funext i
  simp [factorialWordYCount, coordinateWordCount_cons]

theorem factorialWordTCount_cons_t (w : List (Fin 4 ⊕ Fin 3)) (j : Fin 3) :
    factorialWordTCount (Sum.inr j :: w) = factorialWordTCount w + Pi.single j 1 := by
  funext k
  rw [factorialWordTCount, coordinateWordCount_cons]
  by_cases hjk : j = k <;> simp [factorialWordTCount, Pi.add_apply, hjk]

theorem factorialWordYCount_mixedMultiIndexWord (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) :
    factorialWordYCount (mixedMultiIndexWord α β) = α := by
  funext i
  exact mixedMultiIndexWord_count_y α β i

theorem factorialWordTCount_mixedMultiIndexWord (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) :
    factorialWordTCount (mixedMultiIndexWord α β) = β := by
  funext j
  exact mixedMultiIndexWord_count_t α β j

def mixedMultiIndexWordFamily
    (F : (Fin 4 → ℕ) → (Fin 3 → ℕ) → Space (Fin 3) → ℂ)
    (w : List (Fin 4 ⊕ Fin 3)) : Space (Fin 3) → ℂ :=
  F (factorialWordYCount w) (factorialWordTCount w)

theorem mixedMultiIndexWordFamily_nil
    (F : (Fin 4 → ℕ) → (Fin 3 → ℕ) → Space (Fin 3) → ℂ) :
    mixedMultiIndexWordFamily F [] = F 0 0 := by
  rw [mixedMultiIndexWordFamily, factorialWordYCount_nil, factorialWordTCount_nil]

theorem mixedMultiIndexWordFamily_canonical
    (F : (Fin 4 → ℕ) → (Fin 3 → ℕ) → Space (Fin 3) → ℂ)
    (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) :
    mixedMultiIndexWordFamily F (mixedMultiIndexWord α β) = F α β := by
  rw [mixedMultiIndexWordFamily, factorialWordYCount_mixedMultiIndexWord,
    factorialWordTCount_mixedMultiIndexWord]

theorem mixedMultiIndexWordFamily_budget
    {Ω : Set (Space (Fin 3))} {m : ℕ} {W : ℝ}
    (F : (Fin 4 → ℕ) → (Fin 3 → ℕ) → Space (Fin 3) → ℂ)
    (hF : ∀ α β, (∑ i, α i) + (∑ j, β j) ≤ m → RegionL2Budget (F α β) Ω W)
    (w : List (Fin 4 ⊕ Fin 3)) (hw : w.length ≤ m) :
    RegionL2Budget (mixedMultiIndexWordFamily F w) Ω W := by
  exact hF _ _ (by rwa [factorialWordCounts_length])

theorem mixedMultiIndexWordFamily_localD
    {Ω : Set (Space (Fin 3))} {m : ℕ}
    (F : (Fin 4 → ℕ) → (Fin 3 → ℕ) → Space (Fin 3) → ℂ)
    (hY : ∀ α β i, (∑ k, α k) + (∑ j, β j) < m →
      ProductLocalWeakDirectional Ω (F α β) (F (α + Pi.single i 1) β) (yDir i))
    (hT : ∀ α β j, (∑ i, α i) + (∑ k, β k) < m →
      ProductLocalWeakDirectional Ω (F α β) (F α (β + Pi.single j 1)) (tDir j))
    (w : List (Fin 4 ⊕ Fin 3)) (x : Fin 4 ⊕ Fin 3) (hw : w.length < m) :
    ProductLocalWeakDirectional Ω (mixedMultiIndexWordFamily F w)
      (mixedMultiIndexWordFamily F (x :: w)) (productCoordinateDirection x) := by
  cases x with
  | inl i =>
    simpa only [mixedMultiIndexWordFamily, factorialWordYCount_cons_y,
      factorialWordTCount_cons_y, productCoordinateDirection] using
      hY (factorialWordYCount w) (factorialWordTCount w) i
        (by rwa [factorialWordCounts_length])
  | inr j =>
    simpa only [mixedMultiIndexWordFamily, factorialWordYCount_cons_t,
      factorialWordTCount_cons_t, productCoordinateDirection] using
      hT (factorialWordYCount w) (factorialWordTCount w) j
        (by rwa [factorialWordCounts_length])

theorem mixedMultiIndexWeakHk_coordinateWeakHk
    {Ω : Set (Space (Fin 3))} {f : Space (Fin 3) → ℂ} {m : ℕ} {W : ℝ}
    (hf : ProductMixedMultiIndexWeakHk Ω f m W) : ProductCoordinateWeakHk Ω f m W := by
  obtain ⟨F, h0, hBudget, hY, hT⟩ := hf
  refine ⟨mixedMultiIndexWordFamily F, ?_, ?_, ?_⟩
  · exact (mixedMultiIndexWordFamily_nil F).trans h0
  · exact mixedMultiIndexWordFamily_budget F hBudget
  · exact mixedMultiIndexWordFamily_localD F hY hT

theorem mixedMultiIndexWordFamily_append_tt
    (F : (Fin 4 → ℕ) → (Fin 3 → ℕ) → Space (Fin 3) → ℂ)
    (w : List (Fin 4 ⊕ Fin 3)) (j : Fin 3) :
    mixedMultiIndexWordFamily F (w ++ [Sum.inr j, Sum.inr j]) =
      F (factorialWordYCount w) (factorialWordTCount w + Pi.single j 2) := by
  have hy : factorialWordYCount (w ++ [Sum.inr j, Sum.inr j]) = factorialWordYCount w := by
    funext i
    simp [factorialWordYCount, coordinateWordCount, List.countP_append]
  have ht : factorialWordTCount (w ++ [Sum.inr j, Sum.inr j]) =
      factorialWordTCount w + Pi.single j 2 := by
    funext k
    by_cases hjk : j = k <;>
      simp [factorialWordTCount, coordinateWordCount, List.countP_append, Pi.add_apply, hjk]
  rw [mixedMultiIndexWordFamily, hy, ht]

#print axioms mixedMultiIndexWordFamily_localD
#print axioms mixedMultiIndexWeakHk_coordinateWeakHk
#print axioms mixedMultiIndexWordFamily_append_tt
end TheoremT.Continuum.WeakGrushin
