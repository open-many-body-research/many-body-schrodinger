import KSRadialPolynomialReduction_v1
import MvPolynomialCoefficientL1DegreeBound_v1

/-! Coefficient growth of the literal finite radial reduction. The even and
odd outputs partition the input monomials, so their combined coefficient sum
has no extra factor of two. The bound also applies to nonhomogeneous inputs. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum

theorem polynomialCoeffL1_ksRadialSquare :
    polynomialCoeffL1 (ksRadialSquare : MvPolynomial (Fin 3) ℂ) ≤ 3 := by
  unfold ksRadialSquare
  calc
    _ ≤ ∑ i : Fin 3, polynomialCoeffL1 ((MvPolynomial.X i : MvPolynomial (Fin 3) ℂ)^2) :=
      polynomialCoeffL1_sum _ _
    _ ≤ ∑ _i : Fin 3, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      simpa only [polynomialCoeffL1_X, one_pow] using
        polynomialCoeffL1_pow (MvPolynomial.X i : MvPolynomial (Fin 3) ℂ) 2
    _ = 3 := by norm_num

theorem polynomialCoeffL1_ksRadialMonomialCore (d : Fin 4 →₀ ℕ) :
    polynomialCoeffL1 (ksRadialMonomialCore d : MvPolynomial (Fin 3) ℂ) ≤
      (3 : ℝ)^(d (Fin.last 3)/2) := by
  have hprod : polynomialCoeffL1
      (∏ i : Fin 3, (MvPolynomial.X i : MvPolynomial (Fin 3) ℂ)^d i.castSucc) ≤ 1 := by
    calc
      _ ≤ ∏ i : Fin 3, polynomialCoeffL1
          ((MvPolynomial.X i : MvPolynomial (Fin 3) ℂ)^d i.castSucc) :=
        polynomialCoeffL1_prod _ _
      _ ≤ ∏ _i : Fin 3, (1 : ℝ) := by
        apply Finset.prod_le_prod₀ (fun _ _ => polynomialCoeffL1_nonneg _)
        intro i hi
        simpa only [polynomialCoeffL1_X, one_pow] using
          polynomialCoeffL1_pow (MvPolynomial.X i : MvPolynomial (Fin 3) ℂ) (d i.castSucc)
      _ = 1 := by simp
  have hpow : polynomialCoeffL1
      ((ksRadialSquare : MvPolynomial (Fin 3) ℂ)^(d (Fin.last 3)/2)) ≤
      (3 : ℝ)^(d (Fin.last 3)/2) :=
    (polynomialCoeffL1_pow _ _).trans
      (pow_le_pow_left₀ (polynomialCoeffL1_nonneg _) polynomialCoeffL1_ksRadialSquare _)
  unfold ksRadialMonomialCore
  exact (polynomialCoeffL1_mul _ _).trans
    (by simpa only [one_mul] using
      mul_le_mul hprod hpow (polynomialCoeffL1_nonneg _) (by norm_num : (0 : ℝ) ≤ 1))

theorem polynomialCoeffL1_ksRadial_combined_weighted (P : MvPolynomial (Fin 4) ℂ) :
    polynomialCoeffL1 (ksRadialEven P) + polynomialCoeffL1 (ksRadialOdd P) ≤
      ∑ d ∈ P.support, ‖P.coeff d‖ * (3 : ℝ)^(d (Fin.last 3)/2) := by
  classical
  unfold ksRadialEven ksRadialOdd
  apply (add_le_add (polynomialCoeffL1_sum _ _) (polynomialCoeffL1_sum _ _)).trans
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro d hd
  have hcore : polynomialCoeffL1
      (MvPolynomial.C (P.coeff d) * (ksRadialMonomialCore d : MvPolynomial (Fin 3) ℂ)) ≤
      ‖P.coeff d‖ * (3 : ℝ)^(d (Fin.last 3)/2) := by
    apply (polynomialCoeffL1_mul _ _).trans
    rw [polynomialCoeffL1_C]
    exact mul_le_mul_of_nonneg_left (polynomialCoeffL1_ksRadialMonomialCore d) (norm_nonneg _)
  by_cases h : d (Fin.last 3)%2=0 <;>
    simpa only [h, if_true, if_false, mul_zero, polynomialCoeffL1_zero, add_zero, zero_add] using hcore

theorem polynomialCoeffL1_ksRadial_combined_totalDegree (P : MvPolynomial (Fin 4) ℂ) :
    polynomialCoeffL1 (ksRadialEven P) + polynomialCoeffL1 (ksRadialOdd P) ≤
      polynomialCoeffL1 P * (3 : ℝ)^(P.totalDegree/2) := by
  apply (polynomialCoeffL1_ksRadial_combined_weighted P).trans
  rw [polynomialCoeffL1_eq_sum, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro d hd
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3)
  apply Nat.div_le_div_right
  exact (MvPolynomial.le_degreeOf_of_mem_support (Fin.last 3) hd).trans
    (MvPolynomial.degreeOf_le_totalDegree P (Fin.last 3))

theorem polynomialCoeffL1_ksRadial_combined_degree_bound (P : MvPolynomial (Fin 4) ℂ)
    {m : ℕ} (hm : P.totalDegree ≤ m) :
    polynomialCoeffL1 (ksRadialEven P) + polynomialCoeffL1 (ksRadialOdd P) ≤
      polynomialCoeffL1 P * (3 : ℝ)^(m/2) :=
  (polynomialCoeffL1_ksRadial_combined_totalDegree P).trans
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) (Nat.div_le_div_right hm))
      (polynomialCoeffL1_nonneg P))

end TheoremT.Continuum
