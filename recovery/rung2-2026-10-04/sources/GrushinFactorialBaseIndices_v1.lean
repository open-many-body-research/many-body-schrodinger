import GrushinFactorialDerivativeCost_v1
import Mathlib.Data.Pi.Interval
import Mathlib.Order.Interval.Finset.Nat

/-! The exact finite base set for the derivative-cost cutoff. The coordinate
box is only an enumeration device: membership is equivalent to the original
cost bound, including order zero. No norm profile or cardinal bound is asserted. -/
noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum.WeakGrushin

abbrev FactorialBaseIndex := (Fin 4 → ℕ) × (Fin 3 → ℕ)

def factorialBaseIndices (r : ℕ) : Finset FactorialBaseIndex := by
  classical
  exact (Finset.Iic ((fun _ => r), (fun _ => r))).filter
    (fun b => factorialMultiDerivativeCost b.1 b.2 ≤ r)

theorem factorialBaseIndex_coordinate_le_of_cost
    (b : FactorialBaseIndex) (r : ℕ) (h : factorialMultiDerivativeCost b.1 b.2 ≤ r) :
    (∀ i, b.1 i ≤ r) ∧ (∀ j, b.2 j ≤ r) := by
  have ht := factorialDerivativeCost_total_le (∑ i, b.1 i) (∑ j, b.2 j)
  change (∑ i, b.1 i)+(∑ j, b.2 j) ≤ factorialMultiDerivativeCost b.1 b.2 at ht
  constructor
  · intro i
    have hi : b.1 i ≤ ∑ k, b.1 k :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  · intro j
    have hj : b.2 j ≤ ∑ k, b.2 k :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    omega

theorem factorialBaseIndices_mem (r : ℕ) (b : FactorialBaseIndex) :
    b ∈ factorialBaseIndices r ↔ factorialMultiDerivativeCost b.1 b.2 ≤ r := by
  classical
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    obtain ⟨hY, hT⟩ := factorialBaseIndex_coordinate_le_of_cost b r h
    exact Finset.mem_filter.mpr ⟨Finset.mem_Iic.mpr ⟨hY, hT⟩, h⟩

theorem factorialBaseIndices_zero_mem (r : ℕ) :
    ((0 : Fin 4 → ℕ), (0 : Fin 3 → ℕ)) ∈ factorialBaseIndices r := by
  rw [factorialBaseIndices_mem]
  simp [factorialMultiDerivativeCost, factorialDerivativeCost]

theorem factorialBaseIndices_nonempty (r : ℕ) : (factorialBaseIndices r).Nonempty :=
  ⟨(0, 0), factorialBaseIndices_zero_mem r⟩

theorem factorialBaseIndices_mono {r q : ℕ} (hrq : r ≤ q) :
    factorialBaseIndices r ⊆ factorialBaseIndices q := by
  intro b hb
  rw [factorialBaseIndices_mem] at hb ⊢
  exact hb.trans hrq

theorem factorialBaseIndices_coordinate_le {r : ℕ} {b : FactorialBaseIndex}
    (hb : b ∈ factorialBaseIndices r) : (∀ i, b.1 i ≤ r) ∧ (∀ j, b.2 j ≤ r) :=
  factorialBaseIndex_coordinate_le_of_cost b r ((factorialBaseIndices_mem r b).mp hb)

end TheoremT.Continuum.WeakGrushin
