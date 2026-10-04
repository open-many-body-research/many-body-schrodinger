import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-! Executable nonnegative integer pairing for a balanced two-by-two monomial.
The four entries are computed by Nat.min and Nat subtraction, with no choice
or noncomputable selection. Equality of the total exponents proves the exact
row/column margins, including zero and saturated cases. -/
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum

def ksBalancedMonomialPairing (a1 a2 b1 b2 : ℕ) (i j : Fin 2) : ℕ :=
  if i = 0 then
    if j = 0 then min a1 b1 else a1 - min a1 b1
  else
    if j = 0 then b1 - min a1 b1 else min a2 b2

theorem ksBalancedMonomialPairing_entries (a1 a2 b1 b2 : ℕ) :
    ksBalancedMonomialPairing a1 a2 b1 b2 0 0 = min a1 b1 ∧
    ksBalancedMonomialPairing a1 a2 b1 b2 0 1 = a1-min a1 b1 ∧
    ksBalancedMonomialPairing a1 a2 b1 b2 1 0 = b1-min a1 b1 ∧
    ksBalancedMonomialPairing a1 a2 b1 b2 1 1 = min a2 b2 := by
  simp [ksBalancedMonomialPairing]

theorem ksBalancedMonomialPairing_margins {a1 a2 b1 b2 : ℕ}
    (h : a1+a2 = b1+b2) :
    ksBalancedMonomialPairing a1 a2 b1 b2 0 0 +
      ksBalancedMonomialPairing a1 a2 b1 b2 0 1 = a1 ∧
    ksBalancedMonomialPairing a1 a2 b1 b2 1 0 +
      ksBalancedMonomialPairing a1 a2 b1 b2 1 1 = a2 ∧
    ksBalancedMonomialPairing a1 a2 b1 b2 0 0 +
      ksBalancedMonomialPairing a1 a2 b1 b2 1 0 = b1 ∧
    ksBalancedMonomialPairing a1 a2 b1 b2 0 1 +
      ksBalancedMonomialPairing a1 a2 b1 b2 1 1 = b2 := by
  norm_num [ksBalancedMonomialPairing] <;> omega

theorem ksBalancedMonomialPairing_row_sum {a1 a2 b1 b2 : ℕ}
    (h : a1+a2 = b1+b2) (i : Fin 2) :
    (∑ j : Fin 2, ksBalancedMonomialPairing a1 a2 b1 b2 i j) =
      if i = 0 then a1 else a2 := by
  obtain ⟨hr1,hr2,_,_⟩ := ksBalancedMonomialPairing_margins h
  fin_cases i <;> simpa only [Fin.sum_univ_two,ite_true,Fin.zero_eq_one_iff,
    OfNat.ofNat_ne_zero,ite_false] using (by first | exact hr1 | exact hr2)

theorem ksBalancedMonomialPairing_column_sum {a1 a2 b1 b2 : ℕ}
    (h : a1+a2 = b1+b2) (j : Fin 2) :
    (∑ i : Fin 2, ksBalancedMonomialPairing a1 a2 b1 b2 i j) =
      if j = 0 then b1 else b2 := by
  obtain ⟨_,_,hc1,hc2⟩ := ksBalancedMonomialPairing_margins h
  fin_cases j <;> simpa only [Fin.sum_univ_two,ite_true,Fin.zero_eq_one_iff,
    OfNat.ofNat_ne_zero,ite_false] using (by first | exact hc1 | exact hc2)

theorem ksBalancedMonomialPairing_last_eq_remainder {a1 a2 b1 b2 : ℕ}
    (h : a1+a2 = b1+b2) :
    ksBalancedMonomialPairing a1 a2 b1 b2 1 1 =
      (a1+a2)-min a1 b1-(a1-min a1 b1)-(b1-min a1 b1) := by
  norm_num [ksBalancedMonomialPairing] <;> omega

end TheoremT.Continuum
