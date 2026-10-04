import MvPolynomialCoefficientL1DegreeBound_v1
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! Evaluation on a complex polydisc retains the actual homogeneous degree.
In particular a degree-(m-1) odd radial coefficient is never bounded using
the degree-m power of the radius. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum
variable {σ : Type*}

def complexClosedPolydisc (σ : Type*) (r : ℝ) : Set (σ → ℂ) :=
  {X | ∀ i, ‖X i‖ ≤ r}

def complexOpenPolydisc (σ : Type*) (r : ℝ) : Set (σ → ℂ) :=
  {X | ∀ i, ‖X i‖ < r}

theorem homogeneous_polynomial_eval_norm_bound
    (P : MvPolynomial σ ℂ) {m : ℕ} (hP : P.IsHomogeneous m)
    (X : σ → ℂ) {r : ℝ} (hr : 0 ≤ r) (hX : ∀ i, ‖X i‖ ≤ r) :
    ‖MvPolynomial.eval X P‖ ≤ polynomialCoeffL1 P*r^m := by
  classical
  apply (polynomial_eval_norm_weighted P X (fun _ => r) hX).trans_eq
  rw [polynomialCoeffL1_eq_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.prod_pow_eq_pow_sum,← hP.degree_eq_sum_deg_support hd]

theorem homogeneous_polynomial_eval_norm_geometric
    (P : MvPolynomial σ ℂ) {m : ℕ} (hP : P.IsHomogeneous m)
    {M D r : ℝ} (hD : 0 ≤ D) (hr : 0 ≤ r)
    (hL : polynomialCoeffL1 P ≤ M*D^m)
    (X : σ → ℂ) (hX : X ∈ complexClosedPolydisc σ r) :
    ‖MvPolynomial.eval X P‖ ≤ M*(D*r)^m := by
  calc
    _ ≤ polynomialCoeffL1 P*r^m := homogeneous_polynomial_eval_norm_bound P hP X hr hX
    _ ≤ (M*D^m)*r^m := mul_le_mul_of_nonneg_right hL (pow_nonneg hr m)
    _ = _ := by rw [mul_pow]; ring

end TheoremT.Continuum
