import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic

/-! The actual finite set of four-variable monomial exponents of total degree
k, its exact cardinality, and a uniform bound valid also at degree zero. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum

def degreeMonomialExponents4 (k : ℕ) : Finset (Fin 4 →₀ ℕ) :=
  Finset.finsuppAntidiag (Finset.univ : Finset (Fin 4)) k

theorem mem_degreeMonomialExponents4_iff_sum (k : ℕ) (d : Fin 4 →₀ ℕ) :
    d ∈ degreeMonomialExponents4 k ↔ ∑ i : Fin 4, d i = k := by
  simp [degreeMonomialExponents4, Finset.mem_finsuppAntidiag]

theorem mem_degreeMonomialExponents4_iff_finsupp_sum (k : ℕ) (d : Fin 4 →₀ ℕ) :
    d ∈ degreeMonomialExponents4 k ↔ d.sum (fun _ n => n) = k := by
  rw [degreeMonomialExponents4, Finset.mem_finsuppAntidiag']
  simp

theorem card_degreeMonomialExponents4_eq_choose (k : ℕ) :
    (degreeMonomialExponents4 k).card = (k+3).choose k := by
  rw [degreeMonomialExponents4, Finset.card_finsuppAntidiag_nat_eq_choose]
  simp only [Finset.card_univ, Fintype.card_fin]
  congr 1
  omega

theorem card_degreeMonomialExponents4_le_pow (k : ℕ) :
    (degreeMonomialExponents4 k).card ≤ 4^k := by
  rw [card_degreeMonomialExponents4_eq_choose]
  simpa only [Nat.add_comm, Nat.reduceAdd] using Nat.choose_add_le_add_one_pow 3 k

theorem card_degreeMonomialExponents4_zero :
    (degreeMonomialExponents4 0).card = 1 := by
  rw [card_degreeMonomialExponents4_eq_choose]
  norm_num

end TheoremT.Continuum
