import KSBalancedPolynomialDescent_v1
import KSRadialPolynomialHomogeneous_v1

/-! Actual physical finite-polynomial descent under an explicit balanced
support condition. The output polynomials have the corrected degrees m and
m-1 and evaluate on the literal physical KS map. Analytic invariance does
not yet supply the support premise here, and no infinite series is used. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum
open MvPolynomial

def ksPolynomialDescentA (P : MvPolynomial (Fin 4) ℂ) : MvPolynomial (Fin 3) ℂ :=
  ksRadialEven (ksBalancedPolynomialDescent P)

def ksPolynomialDescentB (P : MvPolynomial (Fin 4) ℂ) : MvPolynomial (Fin 3) ℂ :=
  ksRadialOdd (ksBalancedPolynomialDescent P)

theorem ks_balanced_support_half_degree {P : MvPolynomial (Fin 4) ℂ} {m : ℕ}
    (hP : P.IsHomogeneous (2*m))
    (hbalanced : ∀ d ∈ P.support, d 0+d 1=d 2+d 3)
    {d : Fin 4 →₀ ℕ} (hd : d ∈ P.support) : d 0+d 1=m := by
  have hdeg : d.degree=2*m := by
    by_contra hn
    exact (mem_support_iff.mp hd) (hP.coeff_eq_zero hn)
  simp [Finsupp.degree_eq_sum,Fin.sum_univ_succ] at hdeg
  have hb := hbalanced d hd
  omega

theorem ks_balanced_polynomial_descent_homogeneous
    {P : MvPolynomial (Fin 4) ℂ} {m : ℕ}
    (hP : P.IsHomogeneous (2*m))
    (hbalanced : ∀ d ∈ P.support, d 0+d 1=d 2+d 3) :
    (ksPolynomialDescentA P).IsHomogeneous m ∧
      (ksPolynomialDescentB P).IsHomogeneous (m-1) ∧
      (m=0 → ksPolynomialDescentB P=0) := by
  have hD := ksBalancedPolynomialDescent_homogeneous P m hbalanced
    (fun d hd => ks_balanced_support_half_degree hP hbalanced hd)
  refine ⟨ksRadialEven_isHomogeneous hD,ksRadialOdd_isHomogeneous hD,?_⟩
  intro hm
  subst m
  exact ksRadialOdd_eq_zero_of_degree_zero hD

theorem ks_balanced_polynomial_physical_descent
    (P : MvPolynomial (Fin 4) ℂ)
    (hbalanced : ∀ d ∈ P.support, d 0+d 1=d 2+d 3) (y : KSSpace) :
    eval ![ksSpinor y 0,ksSpinor y 1,star (ksSpinor y 0),star (ksSpinor y 1)] P =
      eval (fun k => (ksMap y k : ℂ)) (ksPolynomialDescentA P) +
        (‖y‖^2 : ℝ)*eval (fun k => (ksMap y k : ℂ)) (ksPolynomialDescentB P) := by
  rw [← ksBalancedPolynomialDescent_physical_eval P hbalanced]
  apply ks_radial_polynomial_reduction
  have hr : (‖y‖^2)^2=∑ i : Fin 3, (ksMap y i)^2 := by
    simpa [Fin.sum_univ_succ,add_assoc] using ksMap_radial_relation y
  exact_mod_cast hr

end TheoremT.Continuum
