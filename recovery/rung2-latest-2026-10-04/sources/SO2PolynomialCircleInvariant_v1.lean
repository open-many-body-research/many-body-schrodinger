import MvPolynomialDiagonalAction_v1
import ComplexUnitPhasePowerSeparation_v1
import Mathlib.Algebra.BigOperators.Fin

/-! Invariance under literal unit-phase diagonal substitution forces
equal exponents in two independent variables. Real rotation invariance
is transported to this algebraic statement in a separate module. -/
noncomputable section
set_option autoImplicit false
namespace TheoremT.Continuum
open MvPolynomial

def so2PolynomialCircleAction (u : ℂ) (P : MvPolynomial (Fin 2) ℂ) :
    MvPolynomial (Fin 2) ℂ := polynomialDiagonalAction ![u,star u] P

theorem so2PolynomialCircleAction_coeff (u : ℂ) (P : MvPolynomial (Fin 2) ℂ)
    (d : Fin 2 →₀ ℕ) :
    (so2PolynomialCircleAction u P).coeff d = P.coeff d*u^(d 0)*(star u)^(d 1) := by
  rw [so2PolynomialCircleAction,polynomialDiagonalAction_coeff]
  rw [d.prod_fintype _ (fun _ => pow_zero _)]
  simp [Fin.prod_univ_two,mul_assoc]

theorem so2PolynomialCircleInvariant_balanced_support (P : MvPolynomial (Fin 2) ℂ)
    (hi : ∀ u : ℂ, ‖u‖=1 → so2PolynomialCircleAction u P=P) :
    ∀ d ∈ P.support, d 0=d 1 := by
  intro d hd
  have hc : P.coeff d ≠ 0 := mem_support_iff.mp hd
  apply complex_nat_eq_of_unit_phase_pow_eq
  intro u hu
  have heq := congrArg (fun Q : MvPolynomial (Fin 2) ℂ => Q.coeff d) (hi u hu)
  rw [so2PolynomialCircleAction_coeff] at heq
  have hunit : star u*u=1 := by simpa [hu] using Complex.conj_mul' u
  have hcancel : (star u)^(d 1)*u^(d 1)=1 := by rw [← mul_pow,hunit,one_pow]
  apply mul_left_cancel₀ hc
  calc
    P.coeff d*u^(d 0) = (P.coeff d*u^(d 0))*((star u)^(d 1)*u^(d 1)) := by
      rw [hcancel,mul_one]
    _ = (P.coeff d*u^(d 0)*(star u)^(d 1))*u^(d 1) := by ring
    _ = P.coeff d*u^(d 1) := by rw [heq]

end TheoremT.Continuum
