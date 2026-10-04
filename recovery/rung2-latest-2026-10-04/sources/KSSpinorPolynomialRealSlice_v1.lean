import KSSpinorForwardPolynomial_v1
import KSRealPolynomialToSpinor_v1
import ComplexPolynomialRealSlice_v2

/-! Extension from the actual real spinor slice to the complex polynomial ring.
The literal forward and inverse substitutions are inverse as polynomial maps.
Consequently polynomial equality on all actual real spinors implies equality
in the ring of four independent complex variables. This justifies the transfer
of actual real-coordinate circle invariance to balanced complex support. -/
set_option autoImplicit false
noncomputable section
namespace TheoremT.Continuum
open MvPolynomial

theorem ksSpinorForwardPolynomial_inverse (i : Fin 4) :
    eval₂ C ksSpinorInversePolynomial (ksSpinorForwardPolynomial i) = X i := by
  apply MvPolynomial.funext
  intro z
  rw [← eval_assoc]
  fin_cases i <;> simp [ksSpinorForwardPolynomial,ksSpinorInversePolynomial] <;>
    ring_nf <;> norm_num [Complex.I_sq] <;> ring

theorem ksSpinorPolynomialToReal_left_inverse (P : MvPolynomial (Fin 4) ℂ) :
    ksRealPolynomialToSpinor (ksSpinorPolynomialToReal P) = P := by
  apply MvPolynomial.funext
  intro z
  unfold ksRealPolynomialToSpinor ksSpinorPolynomialToReal
  rw [← eval_assoc,← eval_assoc]
  apply congrArg (fun f : Fin 4 → ℂ => eval f P)
  funext i
  change eval (eval z ∘ ksSpinorInversePolynomial) (ksSpinorForwardPolynomial i) = z i
  rw [eval_assoc,ksSpinorForwardPolynomial_inverse,eval_X]

theorem ksSpinorPolynomialToReal_injective : Function.Injective ksSpinorPolynomialToReal :=
  Function.LeftInverse.injective ksSpinorPolynomialToReal_left_inverse

theorem ksPolynomial_eq_of_spinor_real_eval_eq
    (P Q : MvPolynomial (Fin 4) ℂ)
    (h : ∀ y : KSSpace,
      eval ![ksSpinor y 0,ksSpinor y 1,star (ksSpinor y 0),star (ksSpinor y 1)] P =
      eval ![ksSpinor y 0,ksSpinor y 1,star (ksSpinor y 0),star (ksSpinor y 1)] Q) :
    P=Q := by
  apply ksSpinorPolynomialToReal_injective
  apply complexPolynomial_eq_of_real_eval_eq
  intro x
  let y : KSSpace := WithLp.toLp 2 x
  change eval (fun i => (y i : ℂ)) (ksSpinorPolynomialToReal P) =
    eval (fun i => (y i : ℂ)) (ksSpinorPolynomialToReal Q)
  rw [ksSpinorPolynomialToReal_physical_eval,ksSpinorPolynomialToReal_physical_eval]
  exact h y

theorem ksRealPolynomialToSpinor_circle_invariant
    (P : MvPolynomial (Fin 4) ℂ)
    (hreal : ∀ a b : ℝ, a^2+b^2=1 → ∀ y : KSSpace,
      eval (fun i => (ksCircleAction a b y i : ℂ)) P =
        eval (fun i => (y i : ℂ)) P) :
    ∀ u : ℂ, ‖u‖=1 →
      ksPolynomialCircleAction u (ksRealPolynomialToSpinor P) =
        ksRealPolynomialToSpinor P := by
  intro u hu
  apply ksPolynomial_eq_of_spinor_real_eval_eq
  intro y
  rw [ksPolynomialCircleAction_physical_eval,
    ksRealPolynomialToSpinor_physical_eval,ksRealPolynomialToSpinor_physical_eval]
  apply hreal u.re u.im _ y
  simpa [Complex.normSq_apply,pow_two,hu] using Complex.normSq_eq_norm_sq u

theorem ksRealPolynomialToSpinor_balanced_support
    (P : MvPolynomial (Fin 4) ℂ)
    (hreal : ∀ a b : ℝ, a^2+b^2=1 → ∀ y : KSSpace,
      eval (fun i => (ksCircleAction a b y i : ℂ)) P =
        eval (fun i => (y i : ℂ)) P) :
    ∀ d ∈ (ksRealPolynomialToSpinor P).support, d 0+d 1=d 2+d 3 :=
  ksPolynomialCircleInvariant_balanced_support (ksRealPolynomialToSpinor P)
    (ksRealPolynomialToSpinor_circle_invariant P hreal)

end TheoremT.Continuum
