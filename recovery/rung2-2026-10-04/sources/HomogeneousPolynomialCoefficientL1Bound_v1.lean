import MvPolynomialCoefficientL1DegreeBound_v1
import FiniteHomogeneousMonomialCount_v1
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! A genuine degree-k homogeneous polynomial on four variables has at most
4^k nonzero coefficients. This gives the coefficient majorant used in KS
descent, including the constant and zero-polynomial cases. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum

theorem homogeneous_support_subset_degree_exponents
    (P : MvPolynomial (Fin 4) ℂ) {k : ℕ} (hP : P.IsHomogeneous k) :
    P.support ⊆ degreeMonomialExponents4 k := by
  classical
  intro d hd
  apply Finset.mem_finsuppAntidiag'.mpr
  exact ⟨(hP.degree_eq_sum_deg_support hd).symm,Finset.subset_univ _⟩

theorem homogeneous_support_card_le_four_pow
    (P : MvPolynomial (Fin 4) ℂ) {k : ℕ} (hP : P.IsHomogeneous k) :
    P.support.card ≤ 4^k :=
  (Finset.card_le_card (homogeneous_support_subset_degree_exponents P hP)).trans
    (card_degreeMonomialExponents4_le_pow k)

theorem homogeneous_polynomialCoeffL1_coefficient_bound
    (P : MvPolynomial (Fin 4) ℂ) {k : ℕ} (hP : P.IsHomogeneous k)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ d ∈ P.support, ‖P.coeff d‖ ≤ C) :
    polynomialCoeffL1 P ≤ (4 : ℝ)^k*C := by
  have hcard : (P.support.card : ℝ) ≤ (4 : ℝ)^k := by
    exact_mod_cast homogeneous_support_card_le_four_pow P hP
  rw [polynomialCoeffL1_eq_sum]
  calc
    _ ≤ ∑ _d ∈ P.support, C := Finset.sum_le_sum hc
    _ = (P.support.card : ℝ)*C := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard hC

theorem homogeneous_polynomialCoeffL1_geometric_bound
    (P : MvPolynomial (Fin 4) ℂ) {k : ℕ} (hP : P.IsHomogeneous k)
    {M B : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hc : ∀ d ∈ P.support, ‖P.coeff d‖ ≤ M*B^k) :
    polynomialCoeffL1 P ≤ M*(4*B)^k := by
  have hb := homogeneous_polynomialCoeffL1_coefficient_bound P hP
    (mul_nonneg hM (pow_nonneg hB k)) hc
  convert hb using 1 <;> rw [mul_pow] <;> ring

end TheoremT.Continuum
