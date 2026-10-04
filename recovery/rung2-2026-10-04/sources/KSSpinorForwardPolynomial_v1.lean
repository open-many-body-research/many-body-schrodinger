import KSPolynomialCircleInvariant_v1
import KSDescentSpinorAlgebra_v1

/-! Literal forward spinor substitution from four independent complexified
real coordinates to z1,z2,w1,w2. On real inputs the latter pair are actual
complex conjugates. Polynomial circle action evaluates to the actual real
coordinate circle action; the covariance identity holds for every u. -/
set_option autoImplicit false
noncomputable section
namespace TheoremT.Continuum
open MvPolynomial

def ksSpinorForwardPolynomial : Fin 4 → MvPolynomial (Fin 4) ℂ :=
  ![X 0+C Complex.I*X 1,X 2+C Complex.I*X 3,
    X 0-C Complex.I*X 1,X 2-C Complex.I*X 3]

def ksSpinorPolynomialToReal (P : MvPolynomial (Fin 4) ℂ) :
    MvPolynomial (Fin 4) ℂ :=
  eval₂ C ksSpinorForwardPolynomial P

theorem ksSpinorForwardPolynomial_physical_eval (y : KSSpace) (i : Fin 4) :
    eval (fun k => (y k : ℂ)) (ksSpinorForwardPolynomial i) =
      ![ksSpinor y 0,ksSpinor y 1,star (ksSpinor y 0),star (ksSpinor y 1)] i := by
  fin_cases i <;> apply Complex.ext <;>
    simp [ksSpinorForwardPolynomial,ksSpinor]

theorem ksSpinorPolynomialToReal_physical_eval (P : MvPolynomial (Fin 4) ℂ)
    (y : KSSpace) :
    eval (fun k => (y k : ℂ)) (ksSpinorPolynomialToReal P) =
      eval ![ksSpinor y 0,ksSpinor y 1,star (ksSpinor y 0),star (ksSpinor y 1)] P := by
  unfold ksSpinorPolynomialToReal
  rw [← eval_assoc]
  apply congrArg (fun f : Fin 4 → ℂ => eval f P)
  funext i
  exact ksSpinorForwardPolynomial_physical_eval y i

theorem ksPolynomialCircleAction_physical_eval (u : ℂ)
    (P : MvPolynomial (Fin 4) ℂ) (y : KSSpace) :
    eval ![ksSpinor y 0,ksSpinor y 1,star (ksSpinor y 0),star (ksSpinor y 1)]
      (ksPolynomialCircleAction u P) =
    eval ![ksSpinor (ksCircleAction u.re u.im y) 0,
      ksSpinor (ksCircleAction u.re u.im y) 1,
      star (ksSpinor (ksCircleAction u.re u.im y) 0),
      star (ksSpinor (ksCircleAction u.re u.im y) 1)] P := by
  unfold ksPolynomialCircleAction
  rw [← eval_assoc]
  apply congrArg (fun f : Fin 4 → ℂ => eval f P)
  funext i
  fin_cases i <;>
    simp [ksSpinor_circle_action,Complex.re_add_im,star_mul] <;> ring

end TheoremT.Continuum
