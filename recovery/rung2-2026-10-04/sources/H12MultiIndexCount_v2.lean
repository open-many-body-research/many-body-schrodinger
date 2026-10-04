import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.Card
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic

/-! Finite indexing and norm aggregation for seven-dimensional total order 12.
The stars-and-bars count is symbolic. No derivative family, PDE estimate, or
Sobolev regularity conclusion is asserted by this combinatorial prerequisite.
-/
noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum

def boundedMultiIndex (d m : ℕ) := {alpha : Fin d → ℕ // ∑ i, alpha i ≤ m}

def boundedMultiIndex_slack_equiv (d m : ℕ) :
    boundedMultiIndex d m ≃ {beta : Fin (d+1) → ℕ // ∑ i, beta i = m} where
  toFun alpha := ⟨Fin.cons (m-∑ i, alpha.val i) alpha.val, by
    simp only [Fin.sum_cons]
    exact Nat.sub_add_cancel alpha.property⟩
  invFun beta := ⟨Fin.tail beta.val, by
    have hb := beta.property
    rw [Fin.sum_univ_succ] at hb
    change (∑ i : Fin d, beta.val i.succ) ≤ m
    omega⟩
  left_inv alpha := by
    apply Subtype.ext
    funext i
    rfl
  right_inv beta := by
    apply Subtype.ext
    have hb := beta.property
    rw [Fin.sum_univ_succ] at hb
    have hhead : m - ∑ i, Fin.tail beta.val i = beta.val 0 := by
      change m - ∑ i : Fin d, beta.val i.succ = beta.val 0
      omega
    change Fin.cons (m-∑ i, Fin.tail beta.val i) (Fin.tail beta.val) = beta.val
    rw [hhead]
    exact Fin.cons_self_tail _

def boundedMultiIndex_sym_equiv (d m : ℕ) :
    boundedMultiIndex d m ≃ Sym (Fin (d+1)) m :=
  (boundedMultiIndex_slack_equiv d m).trans (Sym.equivNatSumOfFintype (Fin (d+1)) m).symm

@[instance] def boundedMultiIndex_fintype (d m : ℕ) : Fintype (boundedMultiIndex d m) :=
  Fintype.ofEquiv (Sym (Fin (d+1)) m) (boundedMultiIndex_sym_equiv d m).symm

theorem boundedMultiIndex_card (d m : ℕ) :
    Fintype.card (boundedMultiIndex d m) = (d+m).choose m := by
  calc
    Fintype.card (boundedMultiIndex d m) = Fintype.card (Sym (Fin (d+1)) m) :=
      Fintype.card_congr (boundedMultiIndex_sym_equiv d m)
    _ = (d+m).choose m := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (Sym.card_sym_eq_choose (α := Fin (d+1)) m)

def h12MultiIndices : Finset (boundedMultiIndex 7 12) := Finset.univ

theorem h12MultiIndices_card : h12MultiIndices.card = 50388 := by
  rw [h12MultiIndices, Finset.card_univ, boundedMultiIndex_card]
  rw [Nat.choose_eq_factorial_div_factorial (by norm_num : 12 ≤ 7+12)]
  norm_num [Nat.factorial]

theorem h12MultiIndex_total_order (alpha : boundedMultiIndex 7 12) :
    ∑ i : Fin 7, alpha.val i ≤ 12 := alpha.property

theorem h12MultiIndex_exhaustive (alpha : Fin 7 → ℕ) (h : ∑ i, alpha i ≤ 12) :
    (⟨alpha,h⟩ : boundedMultiIndex 7 12) ∈ h12MultiIndices :=
  @Finset.mem_univ (boundedMultiIndex 7 12) (boundedMultiIndex_fintype 7 12) ⟨alpha,h⟩

def h12MultiIndexNormSq {F : Type*} [SeminormedAddCommGroup F]
    (v : boundedMultiIndex 7 12 → F) : ℝ :=
  ∑ alpha ∈ h12MultiIndices, ‖v alpha‖^2

theorem h12MultiIndexNormSq_nonneg {F : Type*} [SeminormedAddCommGroup F]
    (v : boundedMultiIndex 7 12 → F) : 0 ≤ h12MultiIndexNormSq v :=
  Finset.sum_nonneg (fun alpha _ => sq_nonneg ‖v alpha‖)

theorem h12MultiIndexNormSq_le {F : Type*} [SeminormedAddCommGroup F]
    (v : boundedMultiIndex 7 12 → F) {C : ℝ} (hC : ∀ alpha, ‖v alpha‖ ≤ C) :
    h12MultiIndexNormSq v ≤ 50388 * C^2 := by
  calc
    h12MultiIndexNormSq v ≤ ∑ alpha ∈ h12MultiIndices, C^2 :=
      Finset.sum_le_sum (fun alpha _ => pow_le_pow_left₀ (norm_nonneg _) (hC alpha) 2)
    _ = 50388 * C^2 := by
      rw [Finset.sum_const, nsmul_eq_mul, h12MultiIndices_card]
      norm_num

end TheoremT.Continuum
