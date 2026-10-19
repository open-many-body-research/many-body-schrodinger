import GrushinFactorialLocalProfile_v1
import ProductMixedMultiIndexWordFamily_v1
import SmoothCoordinateSubsetFields7_v1

/-! Exact R24 derivative reserve from the actual weighted finite profile.
An ordinary word costs at most its length plus four. Each mixed tensor subset
adds at most seven letters, so profile order k+11 controls every needed field. -/
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
open MeasureTheory
open scoped BigOperators
namespace TheoremT.Continuum.WeakGrushin

theorem factorialOuterIndices_zero_member :
    ((0,0,0) : FactorialOuterIndex) ∈ factorialOuterIndices := by
  rw [factorialOuterIndices_mem]
  simp [factorialOuterAdmissible]

theorem factorialLocalProfile_unweighted_bound
    {F : FactorialRawJetFamily} {Ω : Set (Space (Fin 3))} {r : ℕ}
    (hF : FactorialLocalMemLp F Ω r) (α : Fin 4 → ℕ) (β : Fin 3 → ℕ)
    (hc : factorialMultiDerivativeCost α β ≤ r) :
    MemLp (F α β) 2 (volume.restrict Ω) ∧
      (eLpNorm (F α β) 2 (volume.restrict Ω)).toReal ≤ factorialLocalProfile F Ω r := by
  have he : factorialShiftedWeightedField F α β (0,0,0) = F α β := by
    funext p
    simp [factorialShiftedWeightedField, factorialYMonomial]
  refine ⟨?_,?_⟩
  · simpa only [he] using hF α β hc (0,0,0) factorialOuterIndices_zero_member
  · have hs : (eLpNorm (factorialShiftedWeightedField F α β (0,0,0)) 2
        (volume.restrict Ω)).toReal ≤ factorialLocalOuterNorm F Ω α β :=
      Finset.single_le_sum (f := fun m => (eLpNorm (factorialShiftedWeightedField F α β m) 2 (volume.restrict Ω)).toReal)
        (fun _ _ => ENNReal.toReal_nonneg) factorialOuterIndices_zero_member
    rw [he] at hs
    exact hs.trans (factorialLocalOuterNorm_le_profile F Ω r α β hc)

theorem factorial_word_cost_le_length_add_four (w : List (Fin 4 ⊕ Fin 3)) :
    factorialMultiDerivativeCost (factorialWordYCount w) (factorialWordTCount w) ≤ w.length+4 := by
  unfold factorialMultiDerivativeCost factorialDerivativeCost
  rw [factorialWordCounts_length]
  exact Nat.add_le_add_left (Nat.min_le_right _ 4) _

theorem factorial_subset_word_cost_le_eleven
    (w : List (Fin 7)) (s : Finset (Fin 7)) :
    factorialMultiDerivativeCost
      (factorialWordYCount ((canonicalSubsetWord7 s ++ w).map sevenCoordinateEquiv))
      (factorialWordTCount ((canonicalSubsetWord7 s ++ w).map sevenCoordinateEquiv)) ≤ w.length+11 := by
  have h := factorial_word_cost_le_length_add_four ((canonicalSubsetWord7 s ++ w).map sevenCoordinateEquiv)
  have hs := canonicalSubsetWord7_append_length s w
  simp only [List.length_map] at h
  omega

theorem factorial_profile_mixed_subset_word_norms
    {F : FactorialRawJetFamily} {Ω : Set (Space (Fin 3))}
    (hF : ∀ r, FactorialLocalMemLp F Ω r)
    (w : List (Fin 7)) (s : Finset (Fin 7)) :
    MemLp (mixedMultiIndexWordFamily F ((canonicalSubsetWord7 s ++ w).map sevenCoordinateEquiv)) 2
      (volume.restrict Ω) ∧
      (eLpNorm (mixedMultiIndexWordFamily F ((canonicalSubsetWord7 s ++ w).map sevenCoordinateEquiv)) 2
        (volume.restrict Ω)).toReal ≤ factorialLocalProfile F Ω (w.length+11) :=
  factorialLocalProfile_unweighted_bound (hF _) _ _ (factorial_subset_word_cost_le_eleven w s)

theorem factorial_profile_word_memLp
    {F : FactorialRawJetFamily} {Ω : Set (Space (Fin 3))}
    (hF : ∀ r, FactorialLocalMemLp F Ω r) (w : List (Fin 4 ⊕ Fin 3)) :
    MemLp (mixedMultiIndexWordFamily F w) 2 (volume.restrict Ω) :=
  (factorialLocalProfile_unweighted_bound (hF _) _ _ (factorial_word_cost_le_length_add_four w)).1

end TheoremT.Continuum.WeakGrushin
