import KSBalancedPolynomialDescent_v1
import MvPolynomialCoefficientL1Scaling_v1

/-! Coefficient control of the literal balanced descent generators and finite
descent sum. These norm bounds hold for every exponent tuple and polynomial;
balance is needed only for the separately proved physical evaluation identity. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum
open MvPolynomial

theorem polynomialCoeffL1_sub {σ : Type*} (p q : MvPolynomial σ ℂ) :
    polynomialCoeffL1 (p-q) ≤ polynomialCoeffL1 p+polynomialCoeffL1 q := by
  simpa only [sub_eq_add_neg, polynomialCoeffL1_neg] using polynomialCoeffL1_add p (-q)

theorem polynomialCoeffL1_ksDescentQuadraticPolynomial (i j : Fin 2) :
    polynomialCoeffL1 (ksDescentQuadraticPolynomial i j) ≤ 1 := by
  have hhalf (p : MvPolynomial (Fin 4) ℂ) (hp : polynomialCoeffL1 p ≤ 2) :
      polynomialCoeffL1 (C (1/2) * p) ≤ 1 := by
    rw [polynomialCoeffL1_C_mul]
    norm_num
    linarith
  fin_cases i <;> fin_cases j <;>
    simp only [ksDescentQuadraticPolynomial, Matrix.cons_val_zero, Matrix.cons_val_one]
  · apply hhalf
    have h := polynomialCoeffL1_add (X 3 : MvPolynomial (Fin 4) ℂ) (X 2)
    rw [polynomialCoeffL1_X, polynomialCoeffL1_X] at h
    norm_num at h
    exact h
  · apply hhalf
    have h := polynomialCoeffL1_add (X 0 : MvPolynomial (Fin 4) ℂ) (C Complex.I * X 1)
    rw [polynomialCoeffL1_X, polynomialCoeffL1_C_mul, polynomialCoeffL1_X] at h
    norm_num at h
    exact h
  · apply hhalf
    have h := polynomialCoeffL1_sub (X 0 : MvPolynomial (Fin 4) ℂ) (C Complex.I * X 1)
    rw [polynomialCoeffL1_X, polynomialCoeffL1_C_mul, polynomialCoeffL1_X] at h
    norm_num at h
    exact h
  · apply hhalf
    have h := polynomialCoeffL1_sub (X 3 : MvPolynomial (Fin 4) ℂ) (X 2)
    rw [polynomialCoeffL1_X, polynomialCoeffL1_X] at h
    norm_num at h
    exact h

theorem polynomialCoeffL1_ksBalancedDescentPolynomial (a1 a2 b1 b2 : ℕ) :
    polynomialCoeffL1 (ksBalancedDescentPolynomial a1 a2 b1 b2) ≤ 1 := by
  have hpow (i j : Fin 2) (k : ℕ) :
      polynomialCoeffL1 ((ksDescentQuadraticPolynomial i j)^k) ≤ 1 := by
    apply (polynomialCoeffL1_pow _ _).trans
    simpa only [one_pow] using pow_le_pow_left₀ (polynomialCoeffL1_nonneg _)
      (polynomialCoeffL1_ksDescentQuadraticPolynomial i j) k
  have hmul (p q : MvPolynomial (Fin 4) ℂ)
      (hp : polynomialCoeffL1 p ≤ 1) (hq : polynomialCoeffL1 q ≤ 1) :
      polynomialCoeffL1 (p*q) ≤ 1 := by
    apply (polynomialCoeffL1_mul p q).trans
    simpa only [one_mul] using
      mul_le_mul hp hq (polynomialCoeffL1_nonneg q) (by norm_num : (0 : ℝ) ≤ 1)
  unfold ksBalancedDescentPolynomial
  exact hmul _ _ (hmul _ _ (hmul _ _ (hpow 0 0 _) (hpow 0 1 _)) (hpow 1 0 _)) (hpow 1 1 _)

theorem polynomialCoeffL1_ksBalancedPolynomialDescent (P : MvPolynomial (Fin 4) ℂ) :
    polynomialCoeffL1 (ksBalancedPolynomialDescent P) ≤ polynomialCoeffL1 P := by
  unfold ksBalancedPolynomialDescent
  apply (polynomialCoeffL1_sum _ _).trans
  rw [polynomialCoeffL1_eq_sum]
  apply Finset.sum_le_sum
  intro d hd
  rw [polynomialCoeffL1_C_mul]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (polynomialCoeffL1_ksBalancedDescentPolynomial (d 0) (d 1) (d 2) (d 3)) (norm_nonneg _)

end TheoremT.Continuum
