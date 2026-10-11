import KSBalancedMonomialFactorization_v1
import KSDescentSpinorAlgebra_v1

/-! Physical balanced monomial descent through the actual KS map.
The computable exponent matrix is reused verbatim. This is a finite algebraic
identity, not yet a theorem about arbitrary invariant series, coefficient
norms, convergence, or the radial A+|X|B reduction. -/
set_option autoImplicit false
namespace TheoremT.Continuum

theorem ksSpinor_balanced_monomial (y : KSSpace)
    {a1 a2 b1 b2 : ℕ} (h : a1+a2=b1+b2) :
    ksSpinor y 0^a1 * ksSpinor y 1^a2 *
      (star (ksSpinor y 0))^b1 * (star (ksSpinor y 1))^b2 =
    (ksDescentQuadratic (fun k => (ksMap y k : ℂ)) (‖y‖^2 : ℝ) 0 0)^
      ksBalancedMonomialPairing a1 a2 b1 b2 0 0 *
    (ksDescentQuadratic (fun k => (ksMap y k : ℂ)) (‖y‖^2 : ℝ) 0 1)^
      ksBalancedMonomialPairing a1 a2 b1 b2 0 1 *
    (ksDescentQuadratic (fun k => (ksMap y k : ℂ)) (‖y‖^2 : ℝ) 1 0)^
      ksBalancedMonomialPairing a1 a2 b1 b2 1 0 *
    (ksDescentQuadratic (fun k => (ksMap y k : ℂ)) (‖y‖^2 : ℝ) 1 1)^
      ksBalancedMonomialPairing a1 a2 b1 b2 1 1 := by
  simpa only [ksSpinor_balanced_quadratic] using
    ksBalancedMonomial_factorization (ksSpinor y 0) (ksSpinor y 1)
      (star (ksSpinor y 0)) (star (ksSpinor y 1)) h

end TheoremT.Continuum
