import KSSpinorPolynomialRealSlice_v1
import ComplexPolynomialRealOpenBox_v1

/-! Local real-coordinate circle invariance suffices for balanced polynomial
support. Equality is extended from an actual positive-radius Euclidean ball,
using a contained real coordinate box and genuine polynomial extensionality.
No global real invariance is assumed in the final theorem. -/
set_option autoImplicit false
noncomputable section
namespace TheoremT.Continuum
open MvPolynomial

theorem ksSpace_norm_lt_of_coordinate_box {r : ℝ} (hr : 0<r) (y : KSSpace)
    (hy : ∀ i : Fin 4, |y i|<r/4) : ‖y‖<r := by
  have hsq (i : Fin 4) : (y i)^2<(r/4)^2 := by
    have h := (sq_lt_sq₀ (abs_nonneg (y i)) (by positivity : 0≤r/4)).2 (hy i)
    simpa only [sq_abs] using h
  have hn : ‖y‖^2=(y 0)^2+(y 1)^2+(y 2)^2+(y 3)^2 := by
    simp [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_succ]
    ring
  apply (sq_lt_sq₀ (norm_nonneg y) (le_of_lt hr)).mp
  have h0 := hsq 0
  have h1 := hsq 1
  have h2 := hsq 2
  have h3 := hsq 3
  nlinarith [sq_pos_of_pos hr]

theorem ksPolynomial_eq_of_spinor_real_ball_eval_eq
    (P Q : MvPolynomial (Fin 4) ℂ) {r : ℝ} (hr : 0<r)
    (h : ∀ y : KSSpace, ‖y‖<r →
      eval ![ksSpinor y 0,ksSpinor y 1,star (ksSpinor y 0),star (ksSpinor y 1)] P =
      eval ![ksSpinor y 0,ksSpinor y 1,star (ksSpinor y 0),star (ksSpinor y 1)] Q) :
    P=Q := by
  apply ksSpinorPolynomialToReal_injective
  apply complexPolynomial_eq_of_real_openBox_eval_eq _ _ (r:=r/4) (by positivity)
  intro x hx
  let y : KSSpace := WithLp.toLp 2 x
  change eval (fun i => (y i : ℂ)) (ksSpinorPolynomialToReal P) =
    eval (fun i => (y i : ℂ)) (ksSpinorPolynomialToReal Q)
  rw [ksSpinorPolynomialToReal_physical_eval,ksSpinorPolynomialToReal_physical_eval]
  exact h y (ksSpace_norm_lt_of_coordinate_box hr y hx)

theorem ksRealPolynomialToSpinor_circle_invariant_of_local
    (P : MvPolynomial (Fin 4) ℂ) {r : ℝ} (hr : 0<r)
    (hreal : ∀ a b : ℝ, a^2+b^2=1 → ∀ y : KSSpace, ‖y‖<r →
      eval (fun i => (ksCircleAction a b y i : ℂ)) P =
        eval (fun i => (y i : ℂ)) P) :
    ∀ u : ℂ, ‖u‖=1 →
      ksPolynomialCircleAction u (ksRealPolynomialToSpinor P) =
        ksRealPolynomialToSpinor P := by
  intro u hu
  apply ksPolynomial_eq_of_spinor_real_ball_eval_eq _ _ hr
  intro y hy
  rw [ksPolynomialCircleAction_physical_eval,
    ksRealPolynomialToSpinor_physical_eval,ksRealPolynomialToSpinor_physical_eval]
  apply hreal u.re u.im _ y hy
  simpa [Complex.normSq_apply,pow_two,hu] using Complex.normSq_eq_norm_sq u

theorem ksRealPolynomialToSpinor_balanced_support_of_local
    (P : MvPolynomial (Fin 4) ℂ) {r : ℝ} (hr : 0<r)
    (hreal : ∀ a b : ℝ, a^2+b^2=1 → ∀ y : KSSpace, ‖y‖<r →
      eval (fun i => (ksCircleAction a b y i : ℂ)) P =
        eval (fun i => (y i : ℂ)) P) :
    ∀ d ∈ (ksRealPolynomialToSpinor P).support, d 0+d 1=d 2+d 3 :=
  ksPolynomialCircleInvariant_balanced_support (ksRealPolynomialToSpinor P)
    (ksRealPolynomialToSpinor_circle_invariant_of_local P hr hreal)

end TheoremT.Continuum
