import KSBalancedMonomialPairing_v1
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.MvPolynomial.Basic

/-! Literal balanced monomial factorization using the executable integer pairing.
The identity holds in every commutative monoid, including complex scalars and
the polynomial ring with four independent complex indeterminates. No variables
need be nonzero, and the degree-zero monomial is included. -/
set_option autoImplicit false
namespace TheoremT.Continuum

theorem ksBalancedMonomial_factorization {R : Type*} [CommMonoid R]
    (z1 z2 w1 w2 : R) {a1 a2 b1 b2 : ℕ} (h : a1+a2=b1+b2) :
    z1^a1 * z2^a2 * w1^b1 * w2^b2 =
      (z1*w1)^ksBalancedMonomialPairing a1 a2 b1 b2 0 0 *
      (z1*w2)^ksBalancedMonomialPairing a1 a2 b1 b2 0 1 *
      (z2*w1)^ksBalancedMonomialPairing a1 a2 b1 b2 1 0 *
      (z2*w2)^ksBalancedMonomialPairing a1 a2 b1 b2 1 1 := by
  obtain ⟨hr1,hr2,hc1,hc2⟩ := ksBalancedMonomialPairing_margins h
  calc
    _ = z1^(ksBalancedMonomialPairing a1 a2 b1 b2 0 0 +
          ksBalancedMonomialPairing a1 a2 b1 b2 0 1) *
        z2^(ksBalancedMonomialPairing a1 a2 b1 b2 1 0 +
          ksBalancedMonomialPairing a1 a2 b1 b2 1 1) *
        w1^(ksBalancedMonomialPairing a1 a2 b1 b2 0 0 +
          ksBalancedMonomialPairing a1 a2 b1 b2 1 0) *
        w2^(ksBalancedMonomialPairing a1 a2 b1 b2 0 1 +
          ksBalancedMonomialPairing a1 a2 b1 b2 1 1) := by
      rw [hr1,hr2,hc1,hc2]
    _ = _ := by
      simp only [pow_add,mul_pow]
      ac_rfl

theorem ksBalancedComplexMonomial_factorization
    (z1 z2 w1 w2 : ℂ) {a1 a2 b1 b2 : ℕ} (h : a1+a2=b1+b2) :
    z1^a1 * z2^a2 * w1^b1 * w2^b2 =
      (z1*w1)^ksBalancedMonomialPairing a1 a2 b1 b2 0 0 *
      (z1*w2)^ksBalancedMonomialPairing a1 a2 b1 b2 0 1 *
      (z2*w1)^ksBalancedMonomialPairing a1 a2 b1 b2 1 0 *
      (z2*w2)^ksBalancedMonomialPairing a1 a2 b1 b2 1 1 :=
  ksBalancedMonomial_factorization z1 z2 w1 w2 h

theorem ksBalancedPolynomialMonomial_factorization
    {a1 a2 b1 b2 : ℕ} (h : a1+a2=b1+b2) :
    (MvPolynomial.X (0 : Fin 4) : MvPolynomial (Fin 4) ℂ)^a1 *
      MvPolynomial.X (1 : Fin 4)^a2 *
      MvPolynomial.X (2 : Fin 4)^b1 *
      MvPolynomial.X (3 : Fin 4)^b2 =
    (MvPolynomial.X (0 : Fin 4)*MvPolynomial.X (2 : Fin 4))^
      ksBalancedMonomialPairing a1 a2 b1 b2 0 0 *
    (MvPolynomial.X (0 : Fin 4)*MvPolynomial.X (3 : Fin 4))^
      ksBalancedMonomialPairing a1 a2 b1 b2 0 1 *
    (MvPolynomial.X (1 : Fin 4)*MvPolynomial.X (2 : Fin 4))^
      ksBalancedMonomialPairing a1 a2 b1 b2 1 0 *
    (MvPolynomial.X (1 : Fin 4)*MvPolynomial.X (3 : Fin 4))^
      ksBalancedMonomialPairing a1 a2 b1 b2 1 1 :=
  ksBalancedMonomial_factorization _ _ _ _ h

end TheoremT.Continuum
