import MvPolynomialCoefficientL1Substitution_v1
import Mathlib.Algebra.MvPolynomial.Degrees

/-! Quantitative substitution cost in the actual total degree, and actual
polynomial value bounds on complex polydiscs. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum
variable {σ τ : Type*}

theorem polynomialCoeffL1_substitution_totalDegree
    (p : MvPolynomial σ ℂ) (G : σ → MvPolynomial τ ℂ)
    {B : ℝ} (hB : 1 ≤ B) (hG : ∀ i, polynomialCoeffL1 (G i) ≤ B) :
    polynomialCoeffL1 (p.eval₂ MvPolynomial.C G) ≤ polynomialCoeffL1 p * B^p.totalDegree := by
  classical
  apply (polynomialCoeffL1_substitution_weighted p G (fun _ => B)
    (fun _ => zero_le_one.trans hB) hG).trans
  rw [polynomialCoeffL1_eq_sum,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro d hd
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  rw [Finset.prod_pow_eq_pow_sum]
  exact pow_le_pow_right₀ hB (MvPolynomial.le_totalDegree hd)

theorem polynomialCoeffL1_substitution_degree_bound
    (p : MvPolynomial σ ℂ) (G : σ → MvPolynomial τ ℂ)
    {B : ℝ} (hB : 1 ≤ B) (hG : ∀ i, polynomialCoeffL1 (G i) ≤ B)
    {n : ℕ} (hn : p.totalDegree ≤ n) :
    polynomialCoeffL1 (p.eval₂ MvPolynomial.C G) ≤ polynomialCoeffL1 p * B^n :=
  (polynomialCoeffL1_substitution_totalDegree p G hB hG).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB hn) (polynomialCoeffL1_nonneg p))

theorem polynomial_eval_norm_weighted (p : MvPolynomial σ ℂ) (z : σ → ℂ)
    (R : σ → ℝ) (hz : ∀ i, ‖z i‖ ≤ R i) :
    ‖MvPolynomial.eval z p‖ ≤ ∑ d ∈ p.support, ‖p.coeff d‖ * ∏ i ∈ d.support, (R i)^(d i) := by
  classical
  rw [MvPolynomial.eval_eq]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro d hd
  rw [norm_mul,norm_prod]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
  intro i hi
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hz i) _

theorem polynomial_eval_norm_le_coeffL1 (p : MvPolynomial σ ℂ) (z : σ → ℂ)
    (hz : ∀ i, ‖z i‖ ≤ 1) :
    ‖MvPolynomial.eval z p‖ ≤ polynomialCoeffL1 p := by
  simpa only [one_pow,Finset.prod_const_one,mul_one,← polynomialCoeffL1_eq_sum] using
    polynomial_eval_norm_weighted p z (fun _ => 1) hz

end TheoremT.Continuum
