import KSRealPolynomialDescent_v1
import KSSpinorPolynomialLocalInvariance_v1

/-! Finite quantitative physical descent from a natural local real-circle
invariance hypothesis. The transformed support condition is discharged by
polynomial extensionality, and every output is the literal finite formula. -/
noncomputable section
set_option autoImplicit false
namespace TheoremT.Continuum
open MvPolynomial

theorem ks_local_invariant_polynomial_quantitative_descent
    (P : MvPolynomial (Fin 4) ℂ) {m : ℕ} (hP : P.IsHomogeneous (2*m))
    {r : ℝ} (hr : 0<r)
    (hreal : ∀ a b : ℝ, a^2+b^2=1 → ∀ y : KSSpace, ‖y‖<r →
      eval (fun i => (ksCircleAction a b y i : ℂ)) P = eval (fun i => (y i : ℂ)) P)
    {M B : ℝ} (hM : 0≤M) (hB : 0≤B)
    (hc : ∀ d ∈ P.support, ‖P.coeff d‖≤M*B^(2*m)) :
    (ksRealPolynomialDescentA P).IsHomogeneous m ∧
      (ksRealPolynomialDescentB P).IsHomogeneous (m-1) ∧
      (m=0 → ksRealPolynomialDescentB P=0) ∧
      polynomialCoeffL1 (ksRealPolynomialDescentA P) +
        polynomialCoeffL1 (ksRealPolynomialDescentB P) ≤ M*(32*B^2)^m ∧
      ∀ y : KSSpace, eval (fun i => (y i : ℂ)) P =
        eval (fun i => (ksMap y i : ℂ)) (ksRealPolynomialDescentA P) +
          (‖y‖^2 : ℝ)*eval (fun i => (ksMap y i : ℂ)) (ksRealPolynomialDescentB P) := by
  have hbal := ksRealPolynomialToSpinor_balanced_support_of_local P hr hreal
  obtain ⟨ha,hb,hzero⟩ := ks_real_polynomial_descent_homogeneous hP hbal
  exact ⟨ha,hb,hzero,polynomialCoeffL1_real_descent_geometric_bound P hP hbal hM hB hc,
    ks_real_polynomial_physical_descent P hbal⟩

end TheoremT.Continuum
