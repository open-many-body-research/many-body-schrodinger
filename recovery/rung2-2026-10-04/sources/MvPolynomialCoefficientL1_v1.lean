import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! The literal finite sum of absolute complex coefficients, without
postulating a normed-ring structure on multivariate polynomials. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum
variable {σ : Type*}

def polynomialCoeffL1 (p : MvPolynomial σ ℂ) : ℝ :=
  p.coeff.sum (fun _ c => ‖c‖)

theorem polynomialCoeffL1_eq_sum (p : MvPolynomial σ ℂ) :
    polynomialCoeffL1 p = ∑ d ∈ p.support, ‖p.coeff d‖ := rfl

theorem polynomialCoeffL1_nonneg (p : MvPolynomial σ ℂ) : 0 ≤ polynomialCoeffL1 p := by
  rw [polynomialCoeffL1_eq_sum]
  exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem polynomialCoeffL1_eq_sum_of_support_subset (p : MvPolynomial σ ℂ)
    (s : Finset (σ →₀ ℕ)) (hs : p.support ⊆ s) :
    polynomialCoeffL1 p = ∑ d ∈ s, ‖p.coeff d‖ := by
  classical
  rw [polynomialCoeffL1_eq_sum]
  exact Finset.sum_subset hs (fun d _ hd => by rw [MvPolynomial.notMem_support_iff.mp hd,norm_zero])

theorem polynomialCoeffL1_zero : polynomialCoeffL1 (0 : MvPolynomial σ ℂ) = 0 := by
  simp [polynomialCoeffL1_eq_sum]

theorem polynomialCoeffL1_monomial (d : σ →₀ ℕ) (c : ℂ) :
    polynomialCoeffL1 (MvPolynomial.monomial d c) = ‖c‖ := by
  exact MvPolynomial.sum_monomial_eq (by simp)

theorem polynomialCoeffL1_C (c : ℂ) :
    polynomialCoeffL1 (MvPolynomial.C c : MvPolynomial σ ℂ) = ‖c‖ := by
  exact polynomialCoeffL1_monomial 0 c

theorem polynomialCoeffL1_one : polynomialCoeffL1 (1 : MvPolynomial σ ℂ) = 1 := by
  rw [MvPolynomial.one_def,polynomialCoeffL1_monomial,norm_one]

theorem polynomialCoeffL1_X (i : σ) : polynomialCoeffL1 (MvPolynomial.X i : MvPolynomial σ ℂ) = 1 := by
  rw [MvPolynomial.X,polynomialCoeffL1_monomial,norm_one]

theorem polynomialCoeffL1_add (p q : MvPolynomial σ ℂ) :
    polynomialCoeffL1 (p+q) ≤ polynomialCoeffL1 p + polynomialCoeffL1 q := by
  classical
  rw [polynomialCoeffL1_eq_sum_of_support_subset (p+q) (p.support ∪ q.support) MvPolynomial.support_add,
    polynomialCoeffL1_eq_sum_of_support_subset p _ Finset.subset_union_left,
    polynomialCoeffL1_eq_sum_of_support_subset q _ Finset.subset_union_right,← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun d _ => by simpa only [AddMonoidAlgebra.coeff_add,Finsupp.add_apply] using norm_add_le (p.coeff d) (q.coeff d))

theorem polynomialCoeffL1_sum {ι : Type*} (s : Finset ι) (p : ι → MvPolynomial σ ℂ) :
    polynomialCoeffL1 (∑ i ∈ s, p i) ≤ ∑ i ∈ s, polynomialCoeffL1 (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [polynomialCoeffL1_zero]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (polynomialCoeffL1_add _ _).trans (add_le_add le_rfl ih)

theorem polynomialCoeffL1_mul (p q : MvPolynomial σ ℂ) :
    polynomialCoeffL1 (p*q) ≤ polynomialCoeffL1 p * polynomialCoeffL1 q := by
  classical
  rw [MvPolynomial.mul_def]
  simp only [MvPolynomial.sum_def]
  calc
    _ ≤ ∑ d ∈ p.support, polynomialCoeffL1
        (∑ e ∈ q.support, MvPolynomial.monomial (d+e) (p.coeff d*q.coeff e)) :=
      polynomialCoeffL1_sum _ _
    _ ≤ ∑ d ∈ p.support, ∑ e ∈ q.support,
        polynomialCoeffL1 (MvPolynomial.monomial (d+e) (p.coeff d*q.coeff e)) :=
      Finset.sum_le_sum (fun _ _ => polynomialCoeffL1_sum _ _)
    _ = _ := by
      simp only [polynomialCoeffL1_monomial,norm_mul,← Finset.mul_sum,← Finset.sum_mul,
        ← polynomialCoeffL1_eq_sum]

theorem polynomialCoeffL1_pow (p : MvPolynomial σ ℂ) (n : ℕ) :
    polynomialCoeffL1 (p^n) ≤ (polynomialCoeffL1 p)^n := by
  induction n with
  | zero => simp [polynomialCoeffL1_one]
  | succ n ih =>
    rw [pow_succ,pow_succ]
    exact (polynomialCoeffL1_mul _ _).trans
      (mul_le_mul_of_nonneg_right ih (polynomialCoeffL1_nonneg p))

theorem polynomialCoeffL1_prod {ι : Type*} (s : Finset ι) (p : ι → MvPolynomial σ ℂ) :
    polynomialCoeffL1 (∏ i ∈ s, p i) ≤ ∏ i ∈ s, polynomialCoeffL1 (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [polynomialCoeffL1_one]
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact (polynomialCoeffL1_mul _ _).trans
      (mul_le_mul_of_nonneg_left ih (polynomialCoeffL1_nonneg _))

end TheoremT.Continuum
