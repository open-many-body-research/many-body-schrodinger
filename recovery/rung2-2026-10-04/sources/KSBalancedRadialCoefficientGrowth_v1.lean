import HomogeneousPolynomialCoefficientL1Bound_v1
import KSBalancedPolynomialCoefficientBound_v1
import KSRadialCoefficientCoarseBound_v1

/-! The complete finite coefficient estimate for balanced spinor descent and
radial reduction. The initial coefficient majorant is explicit; identifying
it with the actual analytic Taylor coefficients is a separate obligation. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum

theorem homogeneous_balanced_row_degree
    (P : MvPolynomial (Fin 4) ℂ) {m : ℕ} (hP : P.IsHomogeneous (2*m))
    (hbalanced : ∀ d ∈ P.support, d 0+d 1=d 2+d 3) :
    ∀ d ∈ P.support, d 0+d 1=m := by
  intro d hd
  have hs := (mem_degreeMonomialExponents4_iff_sum (2*m) d).mp
    (homogeneous_support_subset_degree_exponents P hP hd)
  have hb := hbalanced d hd
  simp only [Fin.sum_univ_succ] at hs
  norm_num at hs
  omega

theorem polynomialCoeffL1_balanced_radial_degree_bound
    (P : MvPolynomial (Fin 4) ℂ) {m : ℕ} (hP : P.IsHomogeneous (2*m))
    (hbalanced : ∀ d ∈ P.support, d 0+d 1=d 2+d 3) :
    polynomialCoeffL1 (ksRadialEven (ksBalancedPolynomialDescent P)) +
        polynomialCoeffL1 (ksRadialOdd (ksBalancedPolynomialDescent P)) ≤
      polynomialCoeffL1 P*(2 : ℝ)^m := by
  have hdeg := ksBalancedPolynomialDescent_homogeneous P m hbalanced
    (homogeneous_balanced_row_degree P hP hbalanced)
  exact (polynomialCoeffL1_ksRadial_combined_coarse_bound _ hdeg.totalDegree_le).trans
    (mul_le_mul_of_nonneg_right (polynomialCoeffL1_ksBalancedPolynomialDescent P) (by positivity))

theorem polynomialCoeffL1_balanced_radial_geometric_bound
    (P : MvPolynomial (Fin 4) ℂ) {m : ℕ} (hP : P.IsHomogeneous (2*m))
    (hbalanced : ∀ d ∈ P.support, d 0+d 1=d 2+d 3)
    {M B : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hc : ∀ d ∈ P.support, ‖P.coeff d‖ ≤ M*B^(2*m)) :
    polynomialCoeffL1 (ksRadialEven (ksBalancedPolynomialDescent P)) +
        polynomialCoeffL1 (ksRadialOdd (ksBalancedPolynomialDescent P)) ≤
      M*(32*B^2)^m := by
  apply (polynomialCoeffL1_balanced_radial_degree_bound P hP hbalanced).trans
  have hn := homogeneous_polynomialCoeffL1_geometric_bound P hP hM hB hc
  calc
    _ ≤ (M*(4*B)^(2*m))*(2 : ℝ)^m := mul_le_mul_of_nonneg_right hn (by positivity)
    _ = _ := by rw [pow_mul,mul_assoc,← mul_pow]; congr 1; congr 1; ring

end TheoremT.Continuum
