import KSBalancedDescentPolynomial_v1

/-! Finite polynomial descent with an explicit balanced-support hypothesis.
The input variables are z1,z2,w1,w2; the output variables are X0,X1,X2,r.
These coordinate meanings are deliberately distinguished despite sharing
the same index type Fin 4. No claim that invariance implies the support
hypothesis, no coefficient bound and no series limit is made here. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum
open MvPolynomial

def ksBalancedPolynomialDescent (P : MvPolynomial (Fin 4) ℂ) :
    MvPolynomial (Fin 4) ℂ :=
  ∑ d ∈ P.support, C (P.coeff d) *
    ksBalancedDescentPolynomial (d 0) (d 1) (d 2) (d 3)

theorem ksBalancedPolynomialDescent_homogeneous (P : MvPolynomial (Fin 4) ℂ)
    (m : ℕ)
    (hbalanced : ∀ d ∈ P.support, d 0+d 1=d 2+d 3)
    (hdegree : ∀ d ∈ P.support, d 0+d 1=m) :
    (ksBalancedPolynomialDescent P).IsHomogeneous m := by
  apply IsHomogeneous.sum
  intro d hd
  rw [← hdegree d hd]
  exact (ksBalancedDescentPolynomial_homogeneous (hbalanced d hd)).C_mul _

theorem ksBalancedPolynomialDescent_physical_eval
    (P : MvPolynomial (Fin 4) ℂ)
    (hbalanced : ∀ d ∈ P.support, d 0+d 1=d 2+d 3) (y : KSSpace) :
    eval (Fin.snoc (fun k => (ksMap y k : ℂ)) (‖y‖^2 : ℝ))
      (ksBalancedPolynomialDescent P) =
    eval ![ksSpinor y 0,ksSpinor y 1,star (ksSpinor y 0),star (ksSpinor y 1)] P := by
  rw [eval_eq' _ P]
  simp only [ksBalancedPolynomialDescent,map_sum,map_mul,eval_C]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← ksSpinor_balanced_descent_polynomial y (hbalanced d hd)]
  simp [Fin.prod_univ_succ,mul_assoc]

end TheoremT.Continuum
