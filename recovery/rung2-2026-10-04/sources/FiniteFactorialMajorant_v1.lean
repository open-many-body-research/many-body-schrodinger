import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Factorial.Basic

/-! Explicit common factorial majorants for a finite family of nonnegative
coefficients. The constants are one plus finite sums, including for an empty
family. No topology, continuity, derivative identification or algorithmic
claim is part of this scalar lemma. -/
noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum
variable {ι : Type*}

def finiteFactorialC (s : Finset ι) (C : ι → ℝ) : ℝ := 1 + ∑ i ∈ s, C i

def finiteFactorialA (s : Finset ι) (A : ι → ℝ) : ℝ := 1 + ∑ i ∈ s, A i

theorem finiteFactorialC_empty (C : ι → ℝ) : finiteFactorialC ∅ C = 1 := by
  simp [finiteFactorialC]

theorem finiteFactorialA_empty (A : ι → ℝ) : finiteFactorialA ∅ A = 1 := by
  simp [finiteFactorialA]

theorem finiteFactorialC_ge_one (s : Finset ι) (C : ι → ℝ)
    (hC : ∀ i ∈ s, 0 ≤ C i) : 1 ≤ finiteFactorialC s C :=
  le_add_of_nonneg_right (Finset.sum_nonneg hC)

theorem finiteFactorialA_ge_one (s : Finset ι) (A : ι → ℝ)
    (hA : ∀ i ∈ s, 0 ≤ A i) : 1 ≤ finiteFactorialA s A :=
  le_add_of_nonneg_right (Finset.sum_nonneg hA)

theorem le_finiteFactorialC (s : Finset ι) (C : ι → ℝ)
    (hC : ∀ i ∈ s, 0 ≤ C i) (i : ι) (hi : i ∈ s) : C i ≤ finiteFactorialC s C := by
  classical
  exact (Finset.single_le_sum hC hi).trans (le_add_of_nonneg_left zero_le_one)

theorem le_finiteFactorialA (s : Finset ι) (A : ι → ℝ)
    (hA : ∀ i ∈ s, 0 ≤ A i) (i : ι) (hi : i ∈ s) : A i ≤ finiteFactorialA s A := by
  classical
  exact (Finset.single_le_sum hA hi).trans (le_add_of_nonneg_left zero_le_one)

theorem finite_factorial_majorant (s : Finset ι) (C A : ι → ℝ)
    (hC : ∀ i ∈ s, 0 ≤ C i) (hA : ∀ i ∈ s, 0 ≤ A i)
    (i : ι) (hi : i ∈ s) (k : ℕ) :
    C i * A i ^ k * (k.factorial : ℝ) ≤
      finiteFactorialC s C * finiteFactorialA s A ^ k * (k.factorial : ℝ) := by
  have hp := pow_le_pow_left₀ (hA i hi) (le_finiteFactorialA s A hA i hi) k
  have hC0 : 0 ≤ finiteFactorialC s C := zero_le_one.trans (finiteFactorialC_ge_one s C hC)
  have hm := mul_le_mul (le_finiteFactorialC s C hC i hi) hp
    (pow_nonneg (hA i hi) k) hC0
  exact mul_le_mul_of_nonneg_right hm (Nat.cast_nonneg k.factorial)

theorem finite_factorial_common_bound (s : Finset ι) (C A : ι → ℝ)
    (hC : ∀ i ∈ s, 0 ≤ C i) (hA : ∀ i ∈ s, 0 ≤ A i) :
    1 ≤ finiteFactorialC s C ∧ 1 ≤ finiteFactorialA s A ∧
      ∀ i ∈ s, ∀ k : ℕ, C i * A i ^ k * (k.factorial : ℝ) ≤
        finiteFactorialC s C * finiteFactorialA s A ^ k * (k.factorial : ℝ) :=
  ⟨finiteFactorialC_ge_one s C hC, finiteFactorialA_ge_one s A hA,
    finite_factorial_majorant s C A hC hA⟩

end TheoremT.Continuum
