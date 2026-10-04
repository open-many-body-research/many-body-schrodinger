import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic
/-! Explicit conversion from the total derivative factorial to coordinate
multiindex factorials. The loss is at most six to the total order for the
six literal physical/spectator coordinates, proved by the multinomial
theorem and exact coordinate-word multiplicity counting. -/
noncomputable section
open scoped BigOperators
namespace ManyBody.S8.MixedAnalytic

theorem multinomial_le_card_pow {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℕ) :
    Nat.multinomial Finset.univ a ≤ (Fintype.card ι)^(∑ i, a i) := by
  have ha : a ∈ Finset.piAntidiag Finset.univ (∑ i, a i) := by
    simp [Finset.mem_piAntidiag]
  have hsum := Finset.sum_pow_eq_sum_piAntidiag Finset.univ
    (fun _ : ι => (1:ℕ)) (∑ i, a i)
  have hs : ∑ b ∈ Finset.piAntidiag (Finset.univ : Finset ι) (∑ i, a i),
      Nat.multinomial Finset.univ b = (Fintype.card ι)^(∑ i, a i) := by
    simpa only [one_pow, Finset.prod_const_one, mul_one, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one, Nat.cast_id] using hsum.symm
  rw [← hs]
  exact Finset.single_le_sum (fun b _ => Nat.zero_le _) ha

theorem total_factorial_le_card_pow_multiFactorial {ι : Type*}
    [Fintype ι] [DecidableEq ι] (a : ι → ℕ) :
    (∑ i, a i).factorial ≤ (Fintype.card ι)^(∑ i, a i)*∏ i, (a i).factorial := by
  rw [← Nat.multinomial_spec Finset.univ a]
  simpa only [mul_comm] using
    Nat.mul_le_mul_left (∏ i, (a i).factorial) (multinomial_le_card_pow a)

def coordinateWordMultiplicity {n : ℕ} (word : Fin n → Fin 3 ⊕ Fin 3)
    (j : Fin 3 ⊕ Fin 3) : ℕ :=
  (Finset.univ.filter (fun i => word i = j)).card

theorem coordinateWordMultiplicity_sum {n : ℕ} (word : Fin n → Fin 3 ⊕ Fin 3) :
    ∑ j, coordinateWordMultiplicity word j = n := by
  have h := Finset.sum_fiberwise Finset.univ word (fun _ : Fin n => (1:ℕ))
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_one,
    coordinateWordMultiplicity, Finset.card_univ, Fintype.card_fin, Nat.cast_id] using h

theorem coordinate_word_factorial_bound {n : ℕ} (word : Fin n → Fin 3 ⊕ Fin 3) :
    n.factorial ≤ 6^n*∏ j, (coordinateWordMultiplicity word j).factorial := by
  have h := total_factorial_le_card_pow_multiFactorial (coordinateWordMultiplicity word)
  simpa only [coordinateWordMultiplicity_sum, Fintype.card_sum, Fintype.card_fin] using h

#print axioms total_factorial_le_card_pow_multiFactorial
#print axioms coordinate_word_factorial_bound
end ManyBody.S8.MixedAnalytic
