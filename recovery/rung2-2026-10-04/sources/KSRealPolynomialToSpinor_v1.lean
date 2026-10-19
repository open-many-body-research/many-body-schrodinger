import KSBalancedPolynomialCoefficientBound_v1

/-! The literal inverse linear substitution from real KS coordinates to
independent complex spinor variables z0,z1,w0,w1. It preserves homogeneous
degree and does not increase the whole coefficient L1 norm. This is not
a claim that each individual coefficient bound is preserved. -/
set_option autoImplicit false
noncomputable section
namespace TheoremT.Continuum
open MvPolynomial

def ksSpinorInversePolynomial : Fin 4 → MvPolynomial (Fin 4) ℂ :=
  ![C (1/2)*(X 0+X 2), C (-Complex.I/2)*(X 0-X 2),
    C (1/2)*(X 1+X 3), C (-Complex.I/2)*(X 1-X 3)]

def ksRealPolynomialToSpinor (P : MvPolynomial (Fin 4) ℂ) : MvPolynomial (Fin 4) ℂ :=
  eval₂ C ksSpinorInversePolynomial P

theorem ksSpinorInversePolynomial_homogeneous (i : Fin 4) :
    (ksSpinorInversePolynomial i).IsHomogeneous 1 := by
  fin_cases i <;> simp only [ksSpinorInversePolynomial,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three]
  · exact ((isHomogeneous_X ℂ 0).add (isHomogeneous_X ℂ 2)).C_mul _
  · exact ((isHomogeneous_X ℂ 0).sub (isHomogeneous_X ℂ 2)).C_mul _
  · exact ((isHomogeneous_X ℂ 1).add (isHomogeneous_X ℂ 3)).C_mul _
  · exact ((isHomogeneous_X ℂ 1).sub (isHomogeneous_X ℂ 3)).C_mul _

theorem ksSpinorInversePolynomial_physical_eval (y : KSSpace) (i : Fin 4) :
    eval ![ksSpinor y 0,ksSpinor y 1,star (ksSpinor y 0),star (ksSpinor y 1)]
      (ksSpinorInversePolynomial i) = (y i : ℂ) := by
  fin_cases i <;> simp [ksSpinorInversePolynomial,ksSpinor] <;>
    apply Complex.ext <;> simp <;> ring

theorem ksRealPolynomialToSpinor_physical_eval (P : MvPolynomial (Fin 4) ℂ)
    (y : KSSpace) :
    eval ![ksSpinor y 0,ksSpinor y 1,star (ksSpinor y 0),star (ksSpinor y 1)]
      (ksRealPolynomialToSpinor P) = eval (fun i => (y i : ℂ)) P := by
  unfold ksRealPolynomialToSpinor
  rw [← eval_assoc]
  apply congrArg (fun f : Fin 4 → ℂ => eval f P)
  funext i
  exact ksSpinorInversePolynomial_physical_eval y i

theorem ksRealPolynomialToSpinor_homogeneous {P : MvPolynomial (Fin 4) ℂ} {k : ℕ}
    (hP : P.IsHomogeneous k) : (ksRealPolynomialToSpinor P).IsHomogeneous k := by
  simpa only [ksRealPolynomialToSpinor,one_mul] using hP.eval₂ C ksSpinorInversePolynomial
    (fun c => isHomogeneous_C _ c) ksSpinorInversePolynomial_homogeneous

theorem polynomialCoeffL1_ksSpinorInversePolynomial (i : Fin 4) :
    polynomialCoeffL1 (ksSpinorInversePolynomial i) ≤ 1 := by
  have hhalf (c : ℂ) (hc : ‖c‖=(1/2 : ℝ)) (p : MvPolynomial (Fin 4) ℂ)
      (hp : polynomialCoeffL1 p ≤ 2) : polynomialCoeffL1 (C c*p) ≤ 1 := by
    rw [polynomialCoeffL1_C_mul,hc]
    linarith
  have hadd (j k : Fin 4) : polynomialCoeffL1 (X j+X k : MvPolynomial (Fin 4) ℂ) ≤ 2 := by
    have h := polynomialCoeffL1_add (X j : MvPolynomial (Fin 4) ℂ) (X k)
    norm_num only [polynomialCoeffL1_X] at h
    exact h
  have hsub (j k : Fin 4) : polynomialCoeffL1 (X j-X k : MvPolynomial (Fin 4) ℂ) ≤ 2 := by
    have h := polynomialCoeffL1_sub (X j : MvPolynomial (Fin 4) ℂ) (X k)
    norm_num only [polynomialCoeffL1_X] at h
    exact h
  fin_cases i <;> simp only [ksSpinorInversePolynomial,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three]
  · exact hhalf _ (by norm_num) _ (hadd 0 2)
  · exact hhalf _ (by norm_num) _ (hsub 0 2)
  · exact hhalf _ (by norm_num) _ (hadd 1 3)
  · exact hhalf _ (by norm_num) _ (hsub 1 3)

theorem polynomialCoeffL1_ksRealPolynomialToSpinor (P : MvPolynomial (Fin 4) ℂ) :
    polynomialCoeffL1 (ksRealPolynomialToSpinor P) ≤ polynomialCoeffL1 P := by
  exact polynomialCoeffL1_substitution_nonexpansive P ksSpinorInversePolynomial
    polynomialCoeffL1_ksSpinorInversePolynomial

end TheoremT.Continuum
