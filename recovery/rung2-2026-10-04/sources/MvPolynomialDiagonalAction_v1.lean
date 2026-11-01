import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic

/-! Literal variable scaling and its exact coefficient formula.
The action is ordinary polynomial substitution X_i -> C(a_i)*X_i.
The proof shows that distinct monomials do not mix under this substitution. -/
set_option autoImplicit false
noncomputable section
namespace TheoremT.Continuum
open MvPolynomial

variable {σ R : Type*} [CommSemiring R]

def polynomialDiagonalAction (a : σ → R) (P : MvPolynomial σ R) : MvPolynomial σ R :=
  eval₂ C (fun i => C (a i)*X i) P

theorem polynomialDiagonalAction_monomial (a : σ → R) (d : σ →₀ ℕ) (c : R) :
    polynomialDiagonalAction a (monomial d c) =
      monomial d (c*d.prod (fun i k => a i^k)) := by
  rw [polynomialDiagonalAction,eval₂_monomial,monomial_eq]
  simp only [mul_pow,
    Finsupp.prod,Finset.prod_mul_distrib,← map_pow,← map_prod,map_mul]
  ring

theorem polynomialDiagonalAction_coeff (a : σ → R) (P : MvPolynomial σ R)
    (d : σ →₀ ℕ) :
    (polynomialDiagonalAction a P).coeff d =
      P.coeff d * d.prod (fun i k => a i^k) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial s c =>
      rw [polynomialDiagonalAction_monomial,coeff_monomial,coeff_monomial]
      by_cases hs : s=d
      · subst s
        simp
      · simp [hs]
  | add P Q hP hQ =>
      simp only [polynomialDiagonalAction,eval₂_add,MvPolynomial.coeff_add] at *
      rw [hP,hQ,add_mul]

end TheoremT.Continuum
