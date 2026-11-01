import Mathlib.Tactic

/-! The exact finite geometric convolution used in the Grushin factorial
induction. This is a conditional scalar implication; the actual PDE recurrence
must still be derived from the weighted norm and genuine weak equations. -/
namespace TheoremT.Continuum
open scoped BigOperators

theorem factorial_majorant_finite_convolution (B : ℝ) (r : ℕ) :
    B^(r+1) + ∑ j ∈ Finset.range r, B^(j+1)*(2*B)^(r-j) =
      B^(r+1)*((2 : ℝ)^(r+1)-1) := by
  induction r with
  | zero => norm_num
  | succ r ih =>
    have hs : (∑ j ∈ Finset.range r, B^(j+1)*(2*B)^(r+1-j)) =
        (2*B)*(∑ j ∈ Finset.range r, B^(j+1)*(2*B)^(r-j)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hjr := Finset.mem_range.mp hj
      rw [show r+1-j = (r-j)+1 by omega, pow_succ]
      ring
    change B^((r+1)+1) + ∑ j ∈ Finset.range (r+1), B^(j+1)*(2*B)^(r+1-j) = _
    rw [Finset.sum_range_succ,hs,show r+1-r = 1 by omega,pow_one]
    calc
      B^((r+1)+1) + ((2*B)*(∑ j ∈ Finset.range r, B^(j+1)*(2*B)^(r-j)) + B^(r+1)*(2*B)) =
          (2*B)*(B^(r+1)+∑ j ∈ Finset.range r, B^(j+1)*(2*B)^(r-j)) + B^((r+1)+1) := by ring
      _ = (2*B)*(B^(r+1)*((2 : ℝ)^(r+1)-1)) + B^((r+1)+1) := by rw [ih]
      _ = B^((r+1)+1)*((2 : ℝ)^((r+1)+1)-1) := by simp only [pow_succ]; ring

theorem factorial_majorant_sequence_bound (B : ℝ) (hB : 1 ≤ B)
    (n0 : ℕ) (d : ℕ → ℝ)
    (hinit : ∀ r, r < n0 → d r ≤ 1)
    (hstep : ∀ r, n0 ≤ r → d r ≤
      B^(r+1)+∑ j ∈ Finset.range r, B^(j+1)*d (r-1-j)) :
    ∀ r, d r ≤ (2*B)^(r+1) := by
  have hBp : 0 ≤ B := by linarith
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    by_cases hr : r < n0
    · exact (hinit r hr).trans (one_le_pow₀ (by linarith : 1 ≤ 2*B))
    · apply (hstep r (by omega)).trans
      calc
        B^(r+1)+∑ j ∈ Finset.range r, B^(j+1)*d (r-1-j) ≤
            B^(r+1)+∑ j ∈ Finset.range r, B^(j+1)*(2*B)^(r-j) := by
          apply add_le_add_right
          apply Finset.sum_le_sum
          intro j hj
          have hjr := Finset.mem_range.mp hj
          have hd := ih (r-1-j) (by omega)
          rw [show r-1-j+1 = r-j by omega] at hd
          exact mul_le_mul_of_nonneg_left hd (pow_nonneg hBp _)
        _ = B^(r+1)*((2 : ℝ)^(r+1)-1) := factorial_majorant_finite_convolution B r
        _ ≤ B^(r+1)*(2 : ℝ)^(r+1) :=
          mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hBp _)
        _ = (2*B)^(r+1) := by rw [mul_pow]; ring

end TheoremT.Continuum
