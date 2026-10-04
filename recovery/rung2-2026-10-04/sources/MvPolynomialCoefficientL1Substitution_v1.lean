import MvPolynomialCoefficientL1_v1

/-! Actual polynomial substitution is bounded by the coefficient-weighted
monomial sum. Cancellation only decreases the resulting coefficient norm. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum
variable {σ τ : Type*}

theorem polynomialCoeffL1_substitution_weighted
    (p : MvPolynomial σ ℂ) (G : σ → MvPolynomial τ ℂ) (R : σ → ℝ)
    (hR : ∀ i, 0 ≤ R i) (hG : ∀ i, polynomialCoeffL1 (G i) ≤ R i) :
    polynomialCoeffL1 (p.eval₂ MvPolynomial.C G) ≤
      ∑ d ∈ p.support, ‖p.coeff d‖ * ∏ i ∈ d.support, (R i)^(d i) := by
  classical
  rw [MvPolynomial.eval₂_eq]
  apply (polynomialCoeffL1_sum _ _).trans
  apply Finset.sum_le_sum
  intro d hd
  calc
    polynomialCoeffL1 (MvPolynomial.C (p.coeff d) * ∏ i ∈ d.support, G i ^ d i) ≤
        polynomialCoeffL1 (MvPolynomial.C (p.coeff d)) *
          polynomialCoeffL1 (∏ i ∈ d.support, G i ^ d i) := polynomialCoeffL1_mul _ _
    _ ≤ ‖p.coeff d‖ * ∏ i ∈ d.support, polynomialCoeffL1 (G i ^ d i) := by
      rw [polynomialCoeffL1_C]
      exact mul_le_mul_of_nonneg_left (polynomialCoeffL1_prod _ _) (norm_nonneg _)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply Finset.prod_le_prod₀ (fun i _ => polynomialCoeffL1_nonneg _)
      intro i hi
      exact (polynomialCoeffL1_pow _ _).trans
        (pow_le_pow_left₀ (polynomialCoeffL1_nonneg _) (hG i) _)

theorem polynomialCoeffL1_substitution_nonexpansive
    (p : MvPolynomial σ ℂ) (G : σ → MvPolynomial τ ℂ)
    (hG : ∀ i, polynomialCoeffL1 (G i) ≤ 1) :
    polynomialCoeffL1 (p.eval₂ MvPolynomial.C G) ≤ polynomialCoeffL1 p := by
  simpa only [one_pow,Finset.prod_const_one,mul_one,← polynomialCoeffL1_eq_sum] using
    polynomialCoeffL1_substitution_weighted p G (fun _ => 1) (fun _ => zero_le_one) hG

theorem polynomialCoeffL1_coefficient_bound (p : MvPolynomial σ ℂ) (d : σ →₀ ℕ) :
    ‖p.coeff d‖ ≤ polynomialCoeffL1 p := by
  classical
  by_cases hd : d ∈ p.support
  · exact Finset.single_le_sum (fun i _ => norm_nonneg (p.coeff i)) hd
  · rw [MvPolynomial.notMem_support_iff.mp hd,norm_zero]
    exact polynomialCoeffL1_nonneg p

theorem polynomialCoeffL1_eq_zero_iff (p : MvPolynomial σ ℂ) :
    polynomialCoeffL1 p = 0 ↔ p = 0 := by
  constructor
  · intro hp
    apply MvPolynomial.ext
    intro d
    have hd := polynomialCoeffL1_coefficient_bound p d
    rw [hp] at hd
    simpa only [AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply] using norm_eq_zero.mp (le_antisymm hd (norm_nonneg _))
  · rintro rfl
    exact polynomialCoeffL1_zero

end TheoremT.Continuum
