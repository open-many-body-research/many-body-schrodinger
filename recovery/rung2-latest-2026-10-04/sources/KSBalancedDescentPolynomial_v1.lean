import KSBalancedMonomialPairingSize_v1
import KSPhysicalBalancedMonomial_v1
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! The actual substituted balanced polynomial in X0,X1,X2,r=X3.
Its coefficients and factors are literal, and its homogeneous degree is the
balanced degree a1+a2. Evaluation connects it to the same physical KS map.
Complex polynomial arithmetic is used as a mathematical object here; the
exponent pairing is the separately verified executable Nat procedure. -/
set_option autoImplicit false
noncomputable section
namespace TheoremT.Continuum
open MvPolynomial

def ksDescentQuadraticPolynomial : Fin 2 → Fin 2 → MvPolynomial (Fin 4) ℂ :=
  ![![C (1/2)*(X 3+X 2), C (1/2)*(X 0+C Complex.I*X 1)],
    ![C (1/2)*(X 0-C Complex.I*X 1), C (1/2)*(X 3-X 2)]]

theorem ksDescentQuadraticPolynomial_homogeneous (i j : Fin 2) :
    (ksDescentQuadraticPolynomial i j).IsHomogeneous 1 := by
  fin_cases i <;> fin_cases j <;>
    simp only [ksDescentQuadraticPolynomial,Matrix.cons_val_zero,Matrix.cons_val_one]
  · exact ((isHomogeneous_X ℂ 3).add (isHomogeneous_X ℂ 2)).C_mul (1/2)
  · exact ((isHomogeneous_X ℂ 0).add
      ((isHomogeneous_X ℂ 1).C_mul Complex.I)).C_mul (1/2)
  · exact ((isHomogeneous_X ℂ 0).sub
      ((isHomogeneous_X ℂ 1).C_mul Complex.I)).C_mul (1/2)
  · exact ((isHomogeneous_X ℂ 3).sub (isHomogeneous_X ℂ 2)).C_mul (1/2)

theorem ksDescentQuadraticPolynomial_eval (X0 : Fin 3 → ℂ) (r : ℂ) (i j : Fin 2) :
    eval (Fin.snoc X0 r) (ksDescentQuadraticPolynomial i j) =
      ksDescentQuadratic X0 r i j := by
  have hs : Fin.snoc X0 r = ![X0 0,X0 1,X0 2,r] := by
    ext k
    fin_cases k <;> rfl
  fin_cases i <;> fin_cases j <;>
    simp [ksDescentQuadraticPolynomial,ksDescentQuadratic,hs] <;> ring

def ksBalancedDescentPolynomial (a1 a2 b1 b2 : ℕ) : MvPolynomial (Fin 4) ℂ :=
  ksDescentQuadraticPolynomial 0 0^ksBalancedMonomialPairing a1 a2 b1 b2 0 0 *
  ksDescentQuadraticPolynomial 0 1^ksBalancedMonomialPairing a1 a2 b1 b2 0 1 *
  ksDescentQuadraticPolynomial 1 0^ksBalancedMonomialPairing a1 a2 b1 b2 1 0 *
  ksDescentQuadraticPolynomial 1 1^ksBalancedMonomialPairing a1 a2 b1 b2 1 1

theorem ksBalancedDescentPolynomial_homogeneous {a1 a2 b1 b2 : ℕ}
    (h : a1+a2=b1+b2) :
    (ksBalancedDescentPolynomial a1 a2 b1 b2).IsHomogeneous (a1+a2) := by
  have hprod := (((ksDescentQuadraticPolynomial_homogeneous 0 0).pow
      (ksBalancedMonomialPairing a1 a2 b1 b2 0 0)).mul
    ((ksDescentQuadraticPolynomial_homogeneous 0 1).pow
      (ksBalancedMonomialPairing a1 a2 b1 b2 0 1))).mul
    ((ksDescentQuadraticPolynomial_homogeneous 1 0).pow
      (ksBalancedMonomialPairing a1 a2 b1 b2 1 0))
  have hprod' := hprod.mul ((ksDescentQuadraticPolynomial_homogeneous 1 1).pow
    (ksBalancedMonomialPairing a1 a2 b1 b2 1 1))
  simpa only [one_mul,ksBalancedMonomialPairing_four_total h,
    ksBalancedDescentPolynomial] using hprod'

theorem ksBalancedDescentPolynomial_eval (X0 : Fin 3 → ℂ) (r : ℂ)
    (a1 a2 b1 b2 : ℕ) :
    eval (Fin.snoc X0 r) (ksBalancedDescentPolynomial a1 a2 b1 b2) =
    (ksDescentQuadratic X0 r 0 0)^ksBalancedMonomialPairing a1 a2 b1 b2 0 0 *
    (ksDescentQuadratic X0 r 0 1)^ksBalancedMonomialPairing a1 a2 b1 b2 0 1 *
    (ksDescentQuadratic X0 r 1 0)^ksBalancedMonomialPairing a1 a2 b1 b2 1 0 *
    (ksDescentQuadratic X0 r 1 1)^ksBalancedMonomialPairing a1 a2 b1 b2 1 1 := by
  simp only [ksBalancedDescentPolynomial,map_mul,map_pow,ksDescentQuadraticPolynomial_eval]

theorem ksSpinor_balanced_descent_polynomial (y : KSSpace)
    {a1 a2 b1 b2 : ℕ} (h : a1+a2=b1+b2) :
    ksSpinor y 0^a1 * ksSpinor y 1^a2 *
      (star (ksSpinor y 0))^b1 * (star (ksSpinor y 1))^b2 =
    eval (Fin.snoc (fun k => (ksMap y k : ℂ)) (‖y‖^2 : ℝ))
      (ksBalancedDescentPolynomial a1 a2 b1 b2) := by
  rw [ksBalancedDescentPolynomial_eval]
  exact ksSpinor_balanced_monomial y h

end TheoremT.Continuum
