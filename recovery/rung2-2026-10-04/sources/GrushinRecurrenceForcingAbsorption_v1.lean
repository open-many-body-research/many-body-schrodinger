import GrushinScaledFallingFactorial_v1
import Mathlib.Data.Nat.Choose.Cast

/-! Exact scalar absorption of the genuine principal and potential commutator
coefficients. This is an arithmetic bridge, not a claim that the localized
PDE graph estimate or the full fixed-gap recurrence has been established. -/
noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum

def grushinFactorialLossSum (A : ℝ) (r : ℕ) (N : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range r,
    A^(j+1)*((r.factorial : ℝ)/((r-1-j).factorial : ℝ))*N (r-1-j)

theorem grushin_choose_factorial_eq_ratio (r j : ℕ) (hj : j ≤ r) :
    (r.choose j : ℝ)*(j.factorial : ℝ) =
      (r.factorial : ℝ)/((r-j).factorial : ℝ) := by
  rw [grushin_factorial_ratio_eq_descFactorial r j hj,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  ring

theorem grushin_choose_loss_sum_eq (A : ℝ) (r : ℕ) (N : ℕ → ℝ) :
    (∑ j ∈ Finset.range r, (r.choose (j+1) : ℝ)*A^(j+1)*
      ((j+1).factorial : ℝ)*N (r-(j+1))) = grushinFactorialLossSum A r N := by
  apply Finset.sum_congr rfl
  intro j hj
  have h := grushin_choose_factorial_eq_ratio r (j+1)
    (by have := Finset.mem_range.mp hj; omega)
  rw [show r-(j+1)=r-1-j by omega] at h ⊢
  calc
    _ = A^(j+1)*((r.choose (j+1) : ℝ)*((j+1).factorial : ℝ))*N (r-1-j) := by ring
    _ = _ := by rw [h]

theorem grushin_factorial_loss_sum_nonneg {A : ℝ} (hA : 0 ≤ A)
    (r : ℕ) (N : ℕ → ℝ) (hN : ∀ k, 0 ≤ N k) :
    0 ≤ grushinFactorialLossSum A r N := by
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (mul_nonneg (pow_nonneg hA _) (by positivity)) (hN _)

theorem grushin_first_two_factorial_losses_le {A : ℝ} (hA : 1 ≤ A)
    (r : ℕ) (hr : 2 ≤ r) (N : ℕ → ℝ) (hN : ∀ k, 0 ≤ N k) :
    (r : ℝ)*N (r-1) + ((r*(r-1) : ℕ) : ℝ)*N (r-2) ≤
      grushinFactorialLossSum A r N := by
  let f : ℕ → ℝ := fun j =>
    A^(j+1)*((r.factorial : ℝ)/((r-1-j).factorial : ℝ))*N (r-1-j)
  have hsum : f 0+f 1 ≤ grushinFactorialLossSum A r N := by
    have hsub : ({0,1} : Finset ℕ) ⊆ Finset.range r := by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl <;> simp only [Finset.mem_range] <;> omega
    have hh := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun j hj hnot => show 0 ≤ f j by
        dsimp [f]
        exact mul_nonneg (mul_nonneg (pow_nonneg (zero_le_one.trans hA) _) (by positivity)) (hN _))
    simpa only [Finset.sum_insert, Finset.mem_singleton, zero_ne_one,
      not_false_eq_true, Finset.sum_singleton, f, grushinFactorialLossSum] using hh
  have hf0 : f 0 = A*(r : ℝ)*N (r-1) := by
    dsimp [f]
    rw [grushin_factorial_ratio_eq_descFactorial r 1 (by omega)]
    simp
  have hf1 : f 1 = A^2*((r*(r-1) : ℕ) : ℝ)*N (r-2) := by
    dsimp [f]
    rw [show r-1-1=r-2 by omega,
      grushin_factorial_ratio_eq_descFactorial r 2 hr]
    simp [Nat.descFactorial, mul_comm]
  have hA2 : 1 ≤ A^2 := one_le_pow₀ hA
  have h0 := mul_le_mul_of_nonneg_right hA
    (mul_nonneg (Nat.cast_nonneg r) (hN (r-1)))
  have h1 := mul_le_mul_of_nonneg_right hA2
    (mul_nonneg (Nat.cast_nonneg (r*(r-1))) (hN (r-2)))
  rw [hf0,hf1] at hsum
  nlinarith

theorem grushin_principal_potential_absorption {A M : ℝ}
    (hA : 1 ≤ A) (hM : 0 ≤ M) (c : ℝ)
    (r : ℕ) (hr : 2 ≤ r) (N : ℕ → ℝ) (hN : ∀ k, 0 ≤ N k) :
    M*(∑ j ∈ Finset.range r, (r.choose (j+1) : ℝ)*A^(j+1)*
      ((j+1).factorial : ℝ)*N (r-(j+1))) +
      6*|c| *(r : ℝ)*N (r-1)+
      3*|c| *((r*(r-1) : ℕ) : ℝ)*N (r-2) ≤
    (M+6*|c|)*grushinFactorialLossSum A r N := by
  rw [grushin_choose_loss_sum_eq]
  have hl := mul_le_mul_of_nonneg_left
    (grushin_first_two_factorial_losses_le hA r hr N hN)
    (show 0 ≤ 6*|c| by positivity)
  have hsecond : 0 ≤ |c| *((r*(r-1) : ℕ) : ℝ)*N (r-2) :=
    mul_nonneg (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _)) (hN _)
  nlinarith

end TheoremT.Continuum
