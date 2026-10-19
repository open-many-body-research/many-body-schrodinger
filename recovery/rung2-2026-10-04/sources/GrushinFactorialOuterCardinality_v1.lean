import GrushinFactorialOuterIndex_v1

/-! Exact cardinality of the advertised weighted outer index set.
The smaller auxiliary enumeration filters each multiindex by total degree
before taking products. Its cardinality is checked by kernel reduction;
the membership bridge proves it is the original set, including all weights.
No native evaluator or added mathematical assumption is used. -/
open scoped BigOperators
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace TheoremT.Continuum.WeakGrushin

def factorialDegreeTwoIndices (k : ℕ) : Finset (Fin k → ℕ) :=
  (Finset.Iic (fun _ => 2)).filter (fun α => (∑ i, α i) ≤ 2)

theorem factorialDegreeTwoIndices_mem (k : ℕ) (α : Fin k → ℕ) :
    α ∈ factorialDegreeTwoIndices k ↔ (∑ i, α i) ≤ 2 := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    refine Finset.mem_filter.mpr ⟨Finset.mem_Iic.mpr ?_, h⟩
    intro i
    exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans h

def factorialOuterDegreeEnumeration : Finset FactorialOuterIndex := by
  letI : DecidablePred factorialOuterAdmissible := fun m => by
    unfold factorialOuterAdmissible
    infer_instance
  exact ((factorialDegreeTwoIndices 4).product
    ((factorialDegreeTwoIndices 3).product (factorialDegreeTwoIndices 4))).filter
      factorialOuterAdmissible

theorem factorialOuterDegreeEnumeration_eq :
    factorialOuterDegreeEnumeration = factorialOuterIndices := by
  letI : DecidablePred factorialOuterAdmissible := fun m => by
    unfold factorialOuterAdmissible
    infer_instance
  ext m
  rw [factorialOuterIndices_mem]
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    have hA : m.1 ∈ factorialDegreeTwoIndices 4 := by
      rw [factorialDegreeTwoIndices_mem]
      have := h.1
      omega
    have hB : m.2.1 ∈ factorialDegreeTwoIndices 3 := by
      rw [factorialDegreeTwoIndices_mem]
      have := h.1
      omega
    have hC : m.2.2 ∈ factorialDegreeTwoIndices 4 := by
      rw [factorialDegreeTwoIndices_mem]
      exact h.2.1
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hA, Finset.mem_product.mpr ⟨hB, hC⟩⟩, h⟩

theorem factorialOuterDegreeEnumeration_card :
    factorialOuterDegreeEnumeration.card = 498 := by
  decide +kernel

theorem factorialOuterIndices_card : factorialOuterIndices.card = 498 := by
  rw [← factorialOuterDegreeEnumeration_eq]
  exact factorialOuterDegreeEnumeration_card

end TheoremT.Continuum.WeakGrushin
