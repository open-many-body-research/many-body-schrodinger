import Mathlib.Data.Nat.Lattice
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega

/-! Exact integer derivative cost from R6, with the index losses consumed
in R8 and the four cases of the principal coefficient commutator R14.
These are finite-index facts, not assertions of differential regularity. -/
noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum.WeakGrushin

def factorialDerivativeCost (A B : ℕ) : ℕ := A+B+min A 4

theorem factorialDerivativeCost_low {A B : ℕ} (hA : A ≤ 4) :
    factorialDerivativeCost A B = 2*A+B := by
  unfold factorialDerivativeCost
  rw [min_eq_left hA]
  omega

theorem factorialDerivativeCost_high {A B : ℕ} (hA : 4 ≤ A) :
    factorialDerivativeCost A B = A+B+4 := by
  unfold factorialDerivativeCost
  rw [min_eq_right hA]

theorem factorialDerivativeCost_total_le (A B : ℕ) :
    A+B ≤ factorialDerivativeCost A B := by
  unfold factorialDerivativeCost
  omega

theorem factorialDerivativeCost_mono {a b A B : ℕ} (ha : a ≤ A) (hb : b ≤ B) :
    factorialDerivativeCost a b ≤ factorialDerivativeCost A B := by
  have hm : min a 4 ≤ min A 4 := min_le_min ha le_rfl
  unfold factorialDerivativeCost
  omega

theorem factorialDerivativeCost_remove {A B a b : ℕ} (ha : a ≤ A) (hb : b ≤ B) :
    factorialDerivativeCost (A-a) (B-b)+(a+b) ≤ factorialDerivativeCost A B := by
  have hm : min (A-a) 4 ≤ min A 4 := min_le_min (Nat.sub_le A a) le_rfl
  unfold factorialDerivativeCost
  omega

theorem factorialDerivativeCost_one_hit_low (B : ℕ) :
    factorialDerivativeCost 0 (B+1)+1 = factorialDerivativeCost 1 B := by
  unfold factorialDerivativeCost
  omega

theorem factorialDerivativeCost_one_hit_high {A B : ℕ} (hA : 2 ≤ A) :
    factorialDerivativeCost (A-2) (B+1)+1 ≤ factorialDerivativeCost A B := by
  have hm : min (A-2) 4 ≤ min A 4 := min_le_min (Nat.sub_le A 2) le_rfl
  unfold factorialDerivativeCost
  omega

theorem factorialDerivativeCost_two_hit_low {A B : ℕ} (hA : 2 ≤ A) (hA3 : A ≤ 3) :
    factorialDerivativeCost (A-2) (B+1)+3 = factorialDerivativeCost A B := by
  unfold factorialDerivativeCost
  omega

theorem factorialDerivativeCost_two_hit_high {A B : ℕ} (hA : 4 ≤ A) :
    factorialDerivativeCost (A-4) (B+2)+2 ≤ factorialDerivativeCost A B := by
  have hm : min (A-4) 4 ≤ min A 4 := min_le_min (Nat.sub_le A 4) le_rfl
  unfold factorialDerivativeCost
  omega

def factorialMultiDerivativeCost (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) : ℕ :=
  factorialDerivativeCost (∑ i, α i) (∑ j, β j)

theorem factorialMultiDerivativeCost_remove
    (α η : Fin 4 → ℕ) (β θ : Fin 3 → ℕ)
    (hη : ∀ i, η i ≤ α i) (hθ : ∀ j, θ j ≤ β j) :
    factorialMultiDerivativeCost (fun i => α i-η i) (fun j => β j-θ j)+
      ((∑ i, η i)+(∑ j, θ j)) ≤ factorialMultiDerivativeCost α β := by
  have hY : (∑ i, η i) ≤ ∑ i, α i := Finset.sum_le_sum (fun i _ => hη i)
  have hT : (∑ j, θ j) ≤ ∑ j, β j := Finset.sum_le_sum (fun j _ => hθ j)
  have hYR : (∑ i, (α i - η i))+(∑ i, η i) = ∑ i, α i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => Nat.sub_add_cancel (hη i))
  have hTR : (∑ j, (β j - θ j))+(∑ j, θ j) = ∑ j, β j := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => Nat.sub_add_cancel (hθ j))
  have hYR' : (∑ i, (α i - η i)) = (∑ i, α i)-(∑ i, η i) := by omega
  have hTR' : (∑ j, (β j - θ j)) = (∑ j, β j)-(∑ j, θ j) := by omega
  unfold factorialMultiDerivativeCost
  rw [hYR',hTR']
  exact factorialDerivativeCost_remove hY hT

end TheoremT.Continuum.WeakGrushin
