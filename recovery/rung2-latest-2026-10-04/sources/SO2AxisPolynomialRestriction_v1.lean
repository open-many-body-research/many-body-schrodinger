import MvPolynomialCoefficientL1Substitution_v1
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! Literal polynomial restriction (X,T)=(x,y,z,0,0,s) to four axis
coordinates, represented as two plane and two spectator coordinates.
It preserves homogeneous degree and does not increase coefficient L1. -/
noncomputable section
set_option autoImplicit false
namespace TheoremT.Continuum
open MvPolynomial

def so2AxisPolynomialGenerator : Fin 3 ⊕ Fin 3 → MvPolynomial (Fin 2 ⊕ Fin 2) ℂ :=
  Sum.elim ![X (.inl 0),X (.inl 1),X (.inr 0)] ![0,0,X (.inr 1)]

def so2AxisPolynomialRestriction (P : MvPolynomial (Fin 3 ⊕ Fin 3) ℂ) :
    MvPolynomial (Fin 2 ⊕ Fin 2) ℂ := eval₂ C so2AxisPolynomialGenerator P

theorem so2AxisPolynomialGenerator_homogeneous (i : Fin 3 ⊕ Fin 3) :
    (so2AxisPolynomialGenerator i).IsHomogeneous 1 := by
  cases i with
  | inl i => fin_cases i <;> exact isHomogeneous_X _ _
  | inr i =>
    fin_cases i
    · exact isHomogeneous_zero _ _ 1
    · exact isHomogeneous_zero _ _ 1
    · exact isHomogeneous_X _ _

theorem so2AxisPolynomialGenerator_coeffL1 (i : Fin 3 ⊕ Fin 3) :
    polynomialCoeffL1 (so2AxisPolynomialGenerator i) ≤ 1 := by
  cases i with
  | inl i => fin_cases i <;> simp [so2AxisPolynomialGenerator,polynomialCoeffL1_X]
  | inr i => fin_cases i <;> simp [so2AxisPolynomialGenerator,polynomialCoeffL1_X,polynomialCoeffL1_zero]

theorem so2AxisPolynomialRestriction_homogeneous
    {P : MvPolynomial (Fin 3 ⊕ Fin 3) ℂ} {n : ℕ} (hP : P.IsHomogeneous n) :
    (so2AxisPolynomialRestriction P).IsHomogeneous n := by
  simpa only [so2AxisPolynomialRestriction,one_mul] using hP.eval₂ C so2AxisPolynomialGenerator
    (fun c => isHomogeneous_C _ c) so2AxisPolynomialGenerator_homogeneous

theorem so2AxisPolynomialRestriction_coeffL1
    (P : MvPolynomial (Fin 3 ⊕ Fin 3) ℂ) :
    polynomialCoeffL1 (so2AxisPolynomialRestriction P) ≤ polynomialCoeffL1 P :=
  polynomialCoeffL1_substitution_nonexpansive P so2AxisPolynomialGenerator so2AxisPolynomialGenerator_coeffL1

theorem so2AxisPolynomialRestriction_eval
    (P : MvPolynomial (Fin 3 ⊕ Fin 3) ℂ) (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) :
    eval (Sum.elim z.1 z.2) (so2AxisPolynomialRestriction P) =
      eval (Sum.elim ![z.1 0,z.1 1,z.2 0] ![0,0,z.2 1]) P := by
  unfold so2AxisPolynomialRestriction
  rw [← eval_assoc]
  apply congrArg (fun f : Fin 3 ⊕ Fin 3 → ℂ => eval f P)
  funext i
  cases i with
  | inl i => fin_cases i <;> simp [so2AxisPolynomialGenerator]
  | inr i => fin_cases i <;> simp [so2AxisPolynomialGenerator]

end TheoremT.Continuum
