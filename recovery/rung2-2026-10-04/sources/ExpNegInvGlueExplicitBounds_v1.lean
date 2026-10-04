import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-! Evaluated low-order bounds for the actual smooth transition building
block. They follow from positive exponential-series terms and exact global
derivative identities, including the flat junction at zero. -/
noncomputable section
open Polynomial
namespace TheoremT.Continuum

theorem nonnegative_monomial_exp_neg_bound {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    x^n * Real.exp (-x) ≤ (n.factorial : ℝ) := by
  have hp : (0 : ℝ) < n.factorial := by positivity
  have hh := (div_le_iff₀ hp).mp (Real.pow_div_factorial_le_exp x hx n)
  have he : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add]; simp
  calc
    x^n * Real.exp (-x) ≤ (Real.exp x * n.factorial) * Real.exp (-x) :=
      mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le
    _ = (n.factorial : ℝ) := by nlinarith [he]

theorem expNegInvGlue_polynomial_bound (x : ℝ) (n : ℕ) :
    x⁻¹^n * expNegInvGlue x ≤ (n.factorial : ℝ) := by
  by_cases hx : x ≤ 0
  · rw [expNegInvGlue.zero_of_nonpos hx, mul_zero]
    positivity
  · rw [expNegInvGlue,ite_eq_right hx]
    exact nonnegative_monomial_exp_neg_bound (inv_nonneg.mpr (le_of_not_ge hx)) n

theorem expNegInvGlue_deriv_formula (x : ℝ) :
    deriv expNegInvGlue x = x⁻¹^2 * expNegInvGlue x := by
  simpa using (expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : ℝ[X]) x).deriv

theorem expNegInvGlue_second_deriv_formula (x : ℝ) :
    deriv (deriv expNegInvGlue) x = (x⁻¹^4-2*x⁻¹^3)*expNegInvGlue x := by
  have hf : deriv expNegInvGlue = fun x => (X^2 : ℝ[X]).eval x⁻¹ * expNegInvGlue x := by
    funext x
    simp only [expNegInvGlue_deriv_formula,eval_pow,eval_X]
  rw [hf]
  have hh := (expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (X^2 : ℝ[X]) x).deriv
  convert hh using 1
  simp
  ring_nf
  simp

theorem expNegInvGlue_deriv_abs_le_two (x : ℝ) : |deriv expNegInvGlue x| ≤ 2 := by
  rw [expNegInvGlue_deriv_formula,abs_of_nonneg (mul_nonneg (sq_nonneg _) (expNegInvGlue.nonneg _))]
  simpa using expNegInvGlue_polynomial_bound x 2

theorem expNegInvGlue_second_deriv_abs_le_thirty_six (x : ℝ) :
    |deriv (deriv expNegInvGlue) x| ≤ 36 := by
  by_cases hx : x ≤ 0
  · rw [expNegInvGlue_second_deriv_formula,expNegInvGlue.zero_of_nonpos hx]
    norm_num
  have hu : 0 ≤ x⁻¹ := inv_nonneg.mpr (le_of_not_ge hx)
  have hg := expNegInvGlue.nonneg x
  have h3 := expNegInvGlue_polynomial_bound x 3
  have h4 := expNegInvGlue_polynomial_bound x 4
  norm_num only [Nat.factorial, Nat.cast_ofNat, Nat.cast_one, Nat.cast_mul] at h3 h4
  rw [expNegInvGlue_second_deriv_formula,sub_mul]
  calc
    |x⁻¹^4*expNegInvGlue x - 2*x⁻¹^3*expNegInvGlue x|
        ≤ |x⁻¹^4*expNegInvGlue x|+|2*x⁻¹^3*expNegInvGlue x| := abs_sub _ _
    _ ≤ 36 := by
      rw [abs_of_nonneg (by positivity),abs_of_nonneg (by positivity)]
      nlinarith

theorem smoothTransition_denom_lower (x : ℝ) :
    (1/16 : ℝ) ≤ expNegInvGlue x + expNegInvGlue (1-x) := by
  have hb : (1/16 : ℝ) ≤ expNegInvGlue (1/2) := by
    have he : Real.exp (2 : ℝ) ≤ 16 := by
      have hh : Real.exp (2 : ℝ) = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]; norm_num
      rw [hh]
      nlinarith [Real.exp_one_lt_three,Real.exp_pos (1 : ℝ)]
    norm_num [expNegInvGlue,Real.exp_neg]
    simpa only [one_div] using
      (inv_le_inv₀ (by norm_num : (0 : ℝ) < 16) (Real.exp_pos (2 : ℝ))).mpr he
  by_cases hx : (1/2 : ℝ) ≤ x
  · have hh := expNegInvGlue.monotone hx
    linarith [expNegInvGlue.nonneg (1-x)]
  · have hh := expNegInvGlue.monotone (show (1/2 : ℝ) ≤ 1-x by linarith)
    linarith [expNegInvGlue.nonneg x]

#print axioms expNegInvGlue_deriv_abs_le_two
#print axioms expNegInvGlue_second_deriv_abs_le_thirty_six
#print axioms smoothTransition_denom_lower
end TheoremT.Continuum
