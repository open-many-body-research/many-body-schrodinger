import SO2ComplexPolynomialCoordinates_v1
import SO2PolynomialCircleInvariant_v1
import ComplexPolynomialRealOpenBox_v1

/-! Actual real planar rotations force balanced polynomial support.
The convention is (x,y) -> (a*x-b*y,b*x+a*y), so v=x+i*y is
multiplied by a+i*b. The second complex variable is independent in the
polynomial ring and evaluates to x-i*y on the real slice. -/
noncomputable section
set_option autoImplicit false
namespace TheoremT.Continuum
open MvPolynomial

def so2RealRotation (a b : ℝ) (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![a*x 0-b*x 1,b*x 0+a*x 1]

def so2RealComplexCoordinates (x : Fin 2 → ℝ) : Fin 2 → ℂ :=
  ![(x 0 : ℂ)+Complex.I*(x 1 : ℂ),(x 0 : ℂ)-Complex.I*(x 1 : ℂ)]

theorem so2PolynomialToCartesian_real_eval (P : MvPolynomial (Fin 2) ℂ)
    (x : Fin 2 → ℝ) :
    eval (fun i => (x i : ℂ)) (so2PolynomialToCartesian P) =
      eval (so2RealComplexCoordinates x) P := by
  unfold so2PolynomialToCartesian
  rw [← eval_assoc]
  apply congrArg (fun f : Fin 2 → ℂ => eval f P)
  funext i
  fin_cases i <;> simp [so2ForwardPolynomial,so2RealComplexCoordinates]

theorem so2PolynomialToBalanced_real_eval (P : MvPolynomial (Fin 2) ℂ)
    (x : Fin 2 → ℝ) :
    eval (so2RealComplexCoordinates x) (so2PolynomialToBalanced P) =
      eval (fun i => (x i : ℂ)) P := by
  rw [← so2PolynomialToCartesian_real_eval,so2PolynomialToCartesian_toBalanced]

theorem so2PolynomialCircleAction_real_eval (u : ℂ) (P : MvPolynomial (Fin 2) ℂ)
    (x : Fin 2 → ℝ) :
    eval (so2RealComplexCoordinates x) (so2PolynomialCircleAction u P) =
      eval (so2RealComplexCoordinates (so2RealRotation u.re u.im x)) P := by
  unfold so2PolynomialCircleAction polynomialDiagonalAction
  rw [← eval_assoc]
  apply congrArg (fun f : Fin 2 → ℂ => eval f P)
  funext i
  fin_cases i <;> simp [so2RealComplexCoordinates,so2RealRotation]
  all_goals apply Complex.ext <;> simp <;> ring

theorem so2Polynomial_eq_of_real_complex_eval_eq (P Q : MvPolynomial (Fin 2) ℂ)
    (h : ∀ x : Fin 2 → ℝ,
      eval (so2RealComplexCoordinates x) P=eval (so2RealComplexCoordinates x) Q) : P=Q := by
  apply Function.LeftInverse.injective so2PolynomialToBalanced_toCartesian
  apply complexPolynomial_eq_of_real_eval_eq
  intro x
  rw [so2PolynomialToCartesian_real_eval,so2PolynomialToCartesian_real_eval]
  exact h x

theorem so2Polynomial_eq_of_real_complex_openBox_eval_eq
    (P Q : MvPolynomial (Fin 2) ℂ) {r : ℝ} (hr : 0<r)
    (h : ∀ x : Fin 2 → ℝ, (∀ i, |x i|<r) →
      eval (so2RealComplexCoordinates x) P=eval (so2RealComplexCoordinates x) Q) : P=Q := by
  apply Function.LeftInverse.injective so2PolynomialToBalanced_toCartesian
  apply complexPolynomial_eq_of_real_openBox_eval_eq _ _ hr
  intro x hx
  rw [so2PolynomialToCartesian_real_eval,so2PolynomialToCartesian_real_eval]
  exact h x hx

theorem so2PolynomialToBalanced_circle_invariant_of_real_rotation
    (P : MvPolynomial (Fin 2) ℂ)
    (hrot : ∀ a b : ℝ, a^2+b^2=1 → ∀ x : Fin 2 → ℝ,
      eval (fun i => (so2RealRotation a b x i : ℂ)) P = eval (fun i => (x i : ℂ)) P) :
    ∀ u : ℂ, ‖u‖=1 → so2PolynomialCircleAction u (so2PolynomialToBalanced P)=
      so2PolynomialToBalanced P := by
  intro u hu
  apply so2Polynomial_eq_of_real_complex_eval_eq
  intro x
  rw [so2PolynomialCircleAction_real_eval,
    so2PolynomialToBalanced_real_eval,so2PolynomialToBalanced_real_eval]
  apply hrot u.re u.im _ x
  simpa [Complex.normSq_apply,pow_two,hu] using Complex.normSq_eq_norm_sq u

theorem so2PolynomialToBalanced_balanced_support_of_real_rotation
    (P : MvPolynomial (Fin 2) ℂ)
    (hrot : ∀ a b : ℝ, a^2+b^2=1 → ∀ x : Fin 2 → ℝ,
      eval (fun i => (so2RealRotation a b x i : ℂ)) P = eval (fun i => (x i : ℂ)) P) :
    ∀ d ∈ (so2PolynomialToBalanced P).support, d 0=d 1 :=
  so2PolynomialCircleInvariant_balanced_support (so2PolynomialToBalanced P)
    (so2PolynomialToBalanced_circle_invariant_of_real_rotation P hrot)

theorem so2PolynomialToBalanced_balanced_support_of_local_real_rotation
    (P : MvPolynomial (Fin 2) ℂ) {r : ℝ} (hr : 0<r)
    (hrot : ∀ a b : ℝ, a^2+b^2=1 → ∀ x : Fin 2 → ℝ, (∀ i, |x i|<r) →
      eval (fun i => (so2RealRotation a b x i : ℂ)) P = eval (fun i => (x i : ℂ)) P) :
    ∀ d ∈ (so2PolynomialToBalanced P).support, d 0=d 1 := by
  apply so2PolynomialCircleInvariant_balanced_support
  intro u hu
  apply so2Polynomial_eq_of_real_complex_openBox_eval_eq _ _ hr
  intro x hx
  rw [so2PolynomialCircleAction_real_eval,
    so2PolynomialToBalanced_real_eval,so2PolynomialToBalanced_real_eval]
  apply hrot u.re u.im _ x hx
  simpa [Complex.normSq_apply,pow_two,hu] using Complex.normSq_eq_norm_sq u

end TheoremT.Continuum
