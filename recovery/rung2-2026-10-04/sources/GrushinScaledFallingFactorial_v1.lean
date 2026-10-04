import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

/-! Scalar normalization by h = rho / ell. The exact falling factorial
identity, rather than an assumed normalization rule, controls every loss
j <= r < ell. These are real inequalities with natural orders. -/
noncomputable section
namespace TheoremT.Continuum

theorem grushin_factorial_ratio_eq_descFactorial (r j : ℕ) (hj : j ≤ r) :
    (r.factorial : ℝ) / ((r-j).factorial : ℝ) = (r.descFactorial j : ℝ) := by
  have hfac : ((r-j).factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (r-j)
  apply (div_eq_iff hfac).2
  exact_mod_cast (Nat.factorial_mul_descFactorial hj).symm.trans (Nat.mul_comm _ _)

theorem grushin_normalization_scale_nonneg {ρ : ℝ} (hρ : 0 ≤ ρ) (ell : ℕ) :
    0 ≤ ρ / (ell : ℝ) := div_nonneg hρ (Nat.cast_nonneg ell)

theorem grushin_normalization_scale_pos {ρ : ℝ} {ell : ℕ}
    (hρ : 0 < ρ) (hell : 0 < ell) : 0 < ρ / (ell : ℝ) :=
  div_pos hρ (by exact_mod_cast hell)

theorem grushin_normalization_scale_le_one {ρ : ℝ} {ell : ℕ}
    (hρ : ρ ≤ 1) (hell : 0 < ell) : ρ / (ell : ℝ) ≤ 1 := by
  have hell0 : (0 : ℝ) < ell := by exact_mod_cast hell
  have hell1 : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  apply (div_le_iff₀ hell0).2
  simpa only [one_mul] using hρ.trans hell1

theorem grushin_normalization_scale_bounds {ρ : ℝ} {ell : ℕ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hell : 0 < ell) :
    0 < ρ / (ell : ℝ) ∧ ρ / (ell : ℝ) ≤ 1 :=
  ⟨grushin_normalization_scale_pos hρ hell,
    grushin_normalization_scale_le_one hρ1 hell⟩

theorem grushin_scaled_falling_factorial_le_rho_pow {ρ : ℝ} {ell r j : ℕ}
    (hρ : 0 ≤ ρ) (hr : r < ell) (hj : j ≤ r) :
    (ρ / (ell : ℝ))^j * (r.factorial : ℝ) / ((r-j).factorial : ℝ) ≤ ρ^j := by
  have hell : (ell : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hr)
  have hd : (r.descFactorial j : ℝ) ≤ (ell : ℝ)^j := by
    exact_mod_cast (Nat.descFactorial_le_pow r j).trans (Nat.pow_le_pow_left hr.le j)
  rw [mul_div_assoc, grushin_factorial_ratio_eq_descFactorial r j hj]
  calc
    _ ≤ (ρ / (ell : ℝ))^j * (ell : ℝ)^j :=
      mul_le_mul_of_nonneg_left hd (pow_nonneg (grushin_normalization_scale_nonneg hρ ell) j)
    _ = ρ^j := by rw [← mul_pow, div_mul_cancel₀ ρ hell]

theorem grushin_scaled_falling_factorial_le_one {ρ : ℝ} {ell r j : ℕ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hr : r < ell) (hj : j ≤ r) :
    (ρ / (ell : ℝ))^j * (r.factorial : ℝ) / ((r-j).factorial : ℝ) ≤ 1 := by
  exact (grushin_scaled_falling_factorial_le_rho_pow hρ0 hr hj).trans
    ((pow_le_pow_left₀ hρ0 hρ1 j).trans_eq (one_pow j))

theorem grushin_scaled_factorial_le_one {ρ : ℝ} {ell r : ℕ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hr : r < ell) :
    (ρ / (ell : ℝ))^r * (r.factorial : ℝ) ≤ 1 := by
  simpa only [Nat.sub_self, Nat.factorial_zero, Nat.cast_one, div_one] using
    grushin_scaled_falling_factorial_le_one hρ0 hρ1 hr (le_refl r)

end TheoremT.Continuum
