import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Tactic

/-! Exact coefficient and evaluation identities for the pinned sumRingEquiv.
Variables in the left summand are the outer polynomial variables; those in
the right summand are the inner coefficient-polynomial variables. The
coefficient formula retains the literal sumElim exponent vector. -/
set_option autoImplicit false
namespace TheoremT.Continuum
open MvPolynomial

variable {σ τ R : Type*} [CommSemiring R]

theorem mvPolynomial_sumRingEquiv_coeff_coeff (P : MvPolynomial (σ ⊕ τ) R)
    (α : σ →₀ ℕ) (β : τ →₀ ℕ) :
    ((sumRingEquiv R σ τ P).coeff α).coeff β = P.coeff (Finsupp.sumElim α β) := by
  change (AddMonoidAlgebra.mapDomainRingEquiv R
    Finsupp.sumFinsuppAddEquivProdFinsupp P).coeff (α,β) = _
  rw [AddMonoidAlgebra.coeff_mapDomainRingEquiv]
  rfl

theorem mvPolynomial_sumRingEquiv_eval (P : MvPolynomial (σ ⊕ τ) R)
    (X : σ → R) (Y : τ → R) :
    eval₂ (eval Y) X (sumRingEquiv R σ τ P) = eval (Sum.elim X Y) P := by
  have H : (eval₂Hom (eval Y) X).comp (sumRingEquiv R σ τ).toRingHom =
      eval (Sum.elim X Y) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · intro i
      cases i <;> simp
  exact congrArg (fun f : MvPolynomial (σ ⊕ τ) R →+* R => f P) H

end TheoremT.Continuum
