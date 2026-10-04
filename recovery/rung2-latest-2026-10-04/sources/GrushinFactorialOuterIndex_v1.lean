import GrushinFactorialDerivativeCost_v1
import Mathlib.Data.Pi.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Analysis.Normed.Group.Basic

/-! The exact finite outer weighted index set R3. The finite box only
implements enumeration: membership is proved equivalent to the three
advertised total-degree inequalities. Coordinate-square rows inject into
this full set, so their actual norm sum is bounded by the full norm. -/
noncomputable section
open scoped BigOperators
set_option maxRecDepth 4096
namespace TheoremT.Continuum.WeakGrushin

abbrev FactorialOuterIndex := (Fin 4 → ℕ) × (Fin 3 → ℕ) × (Fin 4 → ℕ)

def factorialOuterAdmissible (m : FactorialOuterIndex) : Prop :=
  (∑ i, m.1 i)+(∑ j, m.2.1 j) ≤ 2 ∧
  (∑ i, m.2.2 i) ≤ 2 ∧
  (∑ i, m.1 i)+2*(∑ j, m.2.1 j) ≤ (∑ i, m.2.2 i)+2

def factorialOuterIndices : Finset FactorialOuterIndex := by
  classical
  exact (Finset.Iic ((fun _ => 2),(fun _ => 2),(fun _ => 2))).filter
    factorialOuterAdmissible

theorem factorialOuterIndices_mem (m : FactorialOuterIndex) :
    m ∈ factorialOuterIndices ↔ factorialOuterAdmissible m := by
  classical
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Iic.mpr ?_,h⟩
    have hY (i : Fin 4) : m.1 i ≤ ∑ l, m.1 l :=
      Finset.single_le_sum (fun l _ => Nat.zero_le _) (Finset.mem_univ i)
    have hT (j : Fin 3) : m.2.1 j ≤ ∑ l, m.2.1 l :=
      Finset.single_le_sum (fun l _ => Nat.zero_le _) (Finset.mem_univ j)
    have hG (i : Fin 4) : m.2.2 i ≤ ∑ l, m.2.2 l :=
      Finset.single_le_sum (fun l _ => Nat.zero_le _) (Finset.mem_univ i)
    rcases h with ⟨h1,h2,h3⟩
    refine ⟨?_,?_,?_⟩
    · intro i
      change m.1 i ≤ 2
      have := hY i
      omega
    · intro j
      change m.2.1 j ≤ 2
      have := hT j
      omega
    · intro i
      exact (hG i).trans h2

theorem factorialOuterAdmissible_original (m : FactorialOuterIndex) :
    factorialOuterAdmissible m ↔
      (∑ i, m.1 i)+(∑ j, m.2.1 j) ≤ 2 ∧
      (∑ i, m.2.2 i) ≤ 2 ∧
      (∑ i, m.1 i)+2*(∑ j, m.2.1 j)-2 ≤ ∑ i, m.2.2 i := by
  unfold factorialOuterAdmissible
  omega

def factorialSquareOuterIndex (α : Fin 4 → ℕ) (β : Fin 3 → ℕ)
    (i : Fin 4) : FactorialOuterIndex := (α,β,Pi.single i 2)

theorem factorialSquareOuterIndex_mem (α : Fin 4 → ℕ) (β : Fin 3 → ℕ)
    (h : (∑ i, α i)+(∑ j, β j) ≤ 2) (l : Fin 4) :
    factorialSquareOuterIndex α β l ∈ factorialOuterIndices := by
  rw [factorialOuterIndices_mem]
  unfold factorialOuterAdmissible factorialSquareOuterIndex
  simp only [Finset.sum_pi_single', Finset.mem_univ, ite_true]
  omega

theorem factorialSquareOuterIndex_injective (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) :
    Function.Injective (factorialSquareOuterIndex α β) := by
  intro i j h
  have he : (Pi.single i 2 : Fin 4 → ℕ) = Pi.single j 2 := congrArg (fun m => m.2.2) h
  by_contra hij
  have hp := congrFun he i
  simp [Pi.single_apply, hij, Ne.symm hij] at hp

def factorialOuterNorm {E : Type*} [SeminormedAddCommGroup E]
    (F : FactorialOuterIndex → E) : ℝ := ∑ m ∈ factorialOuterIndices, ‖F m‖

theorem factorialSquareOuterIndex_norm_sum_le {E : Type*} [SeminormedAddCommGroup E]
    (F : FactorialOuterIndex → E) (α : Fin 4 → ℕ) (β : Fin 3 → ℕ)
    (h : (∑ i, α i)+(∑ j, β j) ≤ 2) :
    (∑ l, ‖F (factorialSquareOuterIndex α β l)‖) ≤ factorialOuterNorm F := by
  classical
  apply Finset.sum_le_sum_of_injOn (factorialSquareOuterIndex α β)
    (factorialSquareOuterIndex_injective α β).injOn
  · intro m hm
    rcases Finset.mem_image.mp hm with ⟨l,hl,rfl⟩
    exact factorialSquareOuterIndex_mem α β h l
  · intro l hl
    exact le_rfl
  · intro m hm hnot
    exact norm_nonneg _

end TheoremT.Continuum.WeakGrushin
