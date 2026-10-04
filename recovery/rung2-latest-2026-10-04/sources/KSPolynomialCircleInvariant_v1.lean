import MvPolynomialDiagonalAction_v1
import ComplexUnitPhasePowerSeparation_v1
import Mathlib.Algebra.BigOperators.Fin

/-! Circle-invariant complex polynomials have balanced support.
The four independent variables are z1,z2,w1,w2. The action sends them to
u*z1,u*z2,conj(u)*w1,conj(u)*w2. Invariance here is literal equality in
the complex polynomial ring for every unit phase. Extension from a real
slice or from an analytic function is a separate obligation. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum
open MvPolynomial

def ksPolynomialCircleAction (u : ℂ) (P : MvPolynomial (Fin 4) ℂ) :
    MvPolynomial (Fin 4) ℂ :=
  eval₂ C ![C u*X 0,C u*X 1,C (star u)*X 2,C (star u)*X 3] P

theorem ksPolynomialCircleAction_eq_diagonal (u : ℂ)
    (P : MvPolynomial (Fin 4) ℂ) :
    ksPolynomialCircleAction u P =
      polynomialDiagonalAction ![u,u,star u,star u] P := by
  unfold ksPolynomialCircleAction polynomialDiagonalAction
  congr 1
  ext i
  fin_cases i <;> rfl

theorem ksPolynomialCircleAction_coeff (u : ℂ) (P : MvPolynomial (Fin 4) ℂ)
    (d : Fin 4 →₀ ℕ) :
    (ksPolynomialCircleAction u P).coeff d =
      P.coeff d * u^(d 0+d 1) * (star u)^(d 2+d 3) := by
  rw [ksPolynomialCircleAction_eq_diagonal,polynomialDiagonalAction_coeff]
  rw [d.prod_fintype _ (fun _ => pow_zero _)]
  simp [Fin.prod_univ_succ,pow_add,mul_assoc]

theorem ksPolynomialCircleInvariant_balanced_support
    (P : MvPolynomial (Fin 4) ℂ)
    (hinvariant : ∀ u : ℂ, ‖u‖=1 → ksPolynomialCircleAction u P=P) :
    ∀ d ∈ P.support, d 0+d 1=d 2+d 3 := by
  intro d hd
  have hc : P.coeff d ≠ 0 := MvPolynomial.mem_support_iff.mp hd
  apply complex_nat_eq_of_unit_phase_pow_eq
  intro u hu
  have heq := congrArg (fun Q : MvPolynomial (Fin 4) ℂ => Q.coeff d)
    (hinvariant u hu)
  rw [ksPolynomialCircleAction_coeff] at heq
  have hunit : star u*u=1 := by
    simpa [hu] using Complex.conj_mul' u
  have hcancel : (star u)^(d 2+d 3)*u^(d 2+d 3)=1 := by
    rw [← mul_pow,hunit,one_pow]
  apply mul_left_cancel₀ hc
  calc
    P.coeff d*u^(d 0+d 1) =
        (P.coeff d*u^(d 0+d 1))*((star u)^(d 2+d 3)*u^(d 2+d 3)) := by
      rw [hcancel,mul_one]
    _ = (P.coeff d*u^(d 0+d 1)*(star u)^(d 2+d 3))*u^(d 2+d 3) := by ring
    _ = P.coeff d*u^(d 2+d 3) := by rw [heq]

end TheoremT.Continuum
