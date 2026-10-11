import GrushinFactorialFiniteMajorant_v1

/-! The same finite Grushin majorant with an explicit nonnegative amplitude
and a finite horizon. No division by the amplitude occurs, including at zero.
The scalar recurrence is an explicit premise, not a PDE consequence here. -/
namespace TheoremT.Continuum
open scoped BigOperators

theorem factorial_majorant_amplitude_bound (B S : ℝ) (hB : 1 ≤ B) (hS : 0 ≤ S)
    (n0 ell : ℕ) (d : ℕ → ℝ)
    (hinit : ∀ r, r < ell → r < n0 → d r ≤ S)
    (hstep : ∀ r, r < ell → n0 ≤ r → d r ≤
      S*B^(r+1)+∑ j ∈ Finset.range r, B^(j+1)*d (r-1-j)) :
    ∀ r, r < ell → d r ≤ S*(2*B)^(r+1) := by
  have hBp : 0 ≤ B := by linarith
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro hr
    by_cases hr0 : r < n0
    · exact (hinit r hr hr0).trans
        (le_mul_of_one_le_right hS (one_le_pow₀ (by linarith : 1 ≤ 2*B)))
    · apply (hstep r hr (by omega)).trans
      calc
        S*B^(r+1)+∑ j ∈ Finset.range r, B^(j+1)*d (r-1-j) ≤
            S*B^(r+1)+∑ j ∈ Finset.range r, B^(j+1)*(S*(2*B)^(r-j)) := by
          apply add_le_add_right
          apply Finset.sum_le_sum
          intro j hj
          have hjr := Finset.mem_range.mp hj
          have hd := ih (r-1-j) (by omega) (by omega)
          rw [show r-1-j+1 = r-j by omega] at hd
          exact mul_le_mul_of_nonneg_left hd (pow_nonneg hBp _)
        _ = S*(B^(r+1)+∑ j ∈ Finset.range r, B^(j+1)*(2*B)^(r-j)) := by
          rw [mul_add,Finset.mul_sum]
          congr 1
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = S*(B^(r+1)*((2 : ℝ)^(r+1)-1)) := by
          rw [factorial_majorant_finite_convolution]
        _ ≤ S*(B^(r+1)*(2 : ℝ)^(r+1)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hBp _)) hS
        _ = S*(2*B)^(r+1) := by rw [mul_pow]; ring

#print axioms factorial_majorant_amplitude_bound
end TheoremT.Continuum
