import KSSpinorPolynomialRealSlice_v1

/-! Literal independent complex coordinates v=x+iy and vb=x-iy.
The forward and inverse substitutions are proved inverses. Balanced
support will be a separate explicit algebraic premise, not an assumed
consequence of physical rotation invariance in this module. -/
noncomputable section
set_option autoImplicit false
namespace TheoremT.Continuum
open MvPolynomial

def so2ForwardPolynomial : Fin 2 → MvPolynomial (Fin 2) ℂ :=
  ![X 0+C Complex.I*X 1, X 0-C Complex.I*X 1]

def so2InversePolynomial : Fin 2 → MvPolynomial (Fin 2) ℂ :=
  ![C (1/2)*(X 0+X 1), C (-Complex.I/2)*(X 0-X 1)]

def so2PolynomialToBalanced (P : MvPolynomial (Fin 2) ℂ) :
    MvPolynomial (Fin 2) ℂ := eval₂ C so2InversePolynomial P

def so2PolynomialToCartesian (P : MvPolynomial (Fin 2) ℂ) :
    MvPolynomial (Fin 2) ℂ := eval₂ C so2ForwardPolynomial P

theorem so2InversePolynomial_forward (i : Fin 2) :
    eval₂ C so2ForwardPolynomial (so2InversePolynomial i) = X i := by
  apply MvPolynomial.funext
  intro z
  rw [← eval_assoc]
  fin_cases i <;> simp [so2ForwardPolynomial,so2InversePolynomial] <;>
    ring_nf <;> norm_num [Complex.I_sq] <;> ring

theorem so2ForwardPolynomial_inverse (i : Fin 2) :
    eval₂ C so2InversePolynomial (so2ForwardPolynomial i) = X i := by
  apply MvPolynomial.funext
  intro z
  rw [← eval_assoc]
  fin_cases i <;> simp [so2ForwardPolynomial,so2InversePolynomial] <;>
    ring_nf <;> norm_num [Complex.I_sq] <;> ring

theorem so2PolynomialToCartesian_toBalanced (P : MvPolynomial (Fin 2) ℂ) :
    so2PolynomialToCartesian (so2PolynomialToBalanced P) = P := by
  apply MvPolynomial.funext
  intro z
  unfold so2PolynomialToCartesian so2PolynomialToBalanced
  rw [← eval_assoc,← eval_assoc]
  apply congrArg (fun f : Fin 2 → ℂ => eval f P)
  funext i
  change eval (eval z ∘ so2ForwardPolynomial) (so2InversePolynomial i) = z i
  rw [eval_assoc,so2InversePolynomial_forward,eval_X]

theorem so2PolynomialToBalanced_toCartesian (P : MvPolynomial (Fin 2) ℂ) :
    so2PolynomialToBalanced (so2PolynomialToCartesian P) = P := by
  apply MvPolynomial.funext
  intro z
  unfold so2PolynomialToBalanced so2PolynomialToCartesian
  rw [← eval_assoc,← eval_assoc]
  apply congrArg (fun f : Fin 2 → ℂ => eval f P)
  funext i
  change eval (eval z ∘ so2InversePolynomial) (so2ForwardPolynomial i) = z i
  rw [eval_assoc,so2ForwardPolynomial_inverse,eval_X]

theorem so2InversePolynomial_homogeneous (i : Fin 2) :
    (so2InversePolynomial i).IsHomogeneous 1 := by
  fin_cases i <;> simp only [so2InversePolynomial,Matrix.cons_val_zero,Matrix.cons_val_one]
  · exact ((isHomogeneous_X ℂ 0).add (isHomogeneous_X ℂ 1)).C_mul _
  · exact ((isHomogeneous_X ℂ 0).sub (isHomogeneous_X ℂ 1)).C_mul _

theorem so2PolynomialToBalanced_homogeneous {P : MvPolynomial (Fin 2) ℂ} {k : ℕ}
    (hP : P.IsHomogeneous k) : (so2PolynomialToBalanced P).IsHomogeneous k := by
  simpa only [so2PolynomialToBalanced,one_mul] using
    hP.eval₂ C so2InversePolynomial (fun c => isHomogeneous_C _ c)
      so2InversePolynomial_homogeneous

end TheoremT.Continuum
