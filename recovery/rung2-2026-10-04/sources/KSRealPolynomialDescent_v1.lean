import KSRealPolynomialToSpinor_v1
import KSFinitePhysicalPolynomialDescent_v1
import KSBalancedRadialCoefficientGrowth_v1

/-! Finite descent beginning with the original real-coordinate polynomial.
The balance premise is imposed on its literal spinor substitution. The
coefficient bound is transferred through the whole L1 norm; no individual
coefficient bound is assumed to survive the change of variables. -/
noncomputable section
set_option autoImplicit false
namespace TheoremT.Continuum
open MvPolynomial

def ksRealPolynomialDescentA (P : MvPolynomial (Fin 4) ℂ) :
    MvPolynomial (Fin 3) ℂ := ksPolynomialDescentA (ksRealPolynomialToSpinor P)

def ksRealPolynomialDescentB (P : MvPolynomial (Fin 4) ℂ) :
    MvPolynomial (Fin 3) ℂ := ksPolynomialDescentB (ksRealPolynomialToSpinor P)

theorem ks_real_polynomial_physical_descent (P : MvPolynomial (Fin 4) ℂ)
    (hbalanced : ∀ d ∈ (ksRealPolynomialToSpinor P).support, d 0+d 1=d 2+d 3)
    (y : KSSpace) :
    eval (fun i => (y i : ℂ)) P =
      eval (fun i => (ksMap y i : ℂ)) (ksRealPolynomialDescentA P) +
        (‖y‖^2 : ℝ)*eval (fun i => (ksMap y i : ℂ)) (ksRealPolynomialDescentB P) := by
  rw [← ksRealPolynomialToSpinor_physical_eval P y]
  exact ks_balanced_polynomial_physical_descent (ksRealPolynomialToSpinor P) hbalanced y

theorem ks_real_polynomial_descent_homogeneous
    {P : MvPolynomial (Fin 4) ℂ} {m : ℕ} (hP : P.IsHomogeneous (2*m))
    (hbalanced : ∀ d ∈ (ksRealPolynomialToSpinor P).support, d 0+d 1=d 2+d 3) :
    (ksRealPolynomialDescentA P).IsHomogeneous m ∧
      (ksRealPolynomialDescentB P).IsHomogeneous (m-1) ∧
      (m=0 → ksRealPolynomialDescentB P=0) := by
  exact ks_balanced_polynomial_descent_homogeneous
    (ksRealPolynomialToSpinor_homogeneous hP) hbalanced

theorem polynomialCoeffL1_real_descent_degree_bound
    (P : MvPolynomial (Fin 4) ℂ) {m : ℕ} (hP : P.IsHomogeneous (2*m))
    (hbalanced : ∀ d ∈ (ksRealPolynomialToSpinor P).support, d 0+d 1=d 2+d 3) :
    polynomialCoeffL1 (ksRealPolynomialDescentA P) +
        polynomialCoeffL1 (ksRealPolynomialDescentB P) ≤
      polynomialCoeffL1 P*(2 : ℝ)^m := by
  exact (polynomialCoeffL1_balanced_radial_degree_bound (ksRealPolynomialToSpinor P)
    (ksRealPolynomialToSpinor_homogeneous hP) hbalanced).trans
    (mul_le_mul_of_nonneg_right (polynomialCoeffL1_ksRealPolynomialToSpinor P)
      (by positivity))

theorem polynomialCoeffL1_real_descent_geometric_bound
    (P : MvPolynomial (Fin 4) ℂ) {m : ℕ} (hP : P.IsHomogeneous (2*m))
    (hbalanced : ∀ d ∈ (ksRealPolynomialToSpinor P).support, d 0+d 1=d 2+d 3)
    {M B : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hc : ∀ d ∈ P.support, ‖P.coeff d‖ ≤ M*B^(2*m)) :
    polynomialCoeffL1 (ksRealPolynomialDescentA P) +
        polynomialCoeffL1 (ksRealPolynomialDescentB P) ≤ M*(32*B^2)^m := by
  apply (polynomialCoeffL1_real_descent_degree_bound P hP hbalanced).trans
  have hn := homogeneous_polynomialCoeffL1_geometric_bound P hP hM hB hc
  calc
    _ ≤ (M*(4*B)^(2*m))*(2 : ℝ)^m := mul_le_mul_of_nonneg_right hn (by positivity)
    _ = _ := by rw [pow_mul,mul_assoc,← mul_pow]; congr 1; congr 1; ring

end TheoremT.Continuum
