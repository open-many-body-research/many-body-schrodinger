import KSSpectatorCoefficientPolynomial_v1
import KSSpinorPolynomialRealSlice_v1
import KSCircleContinuousLinear_v1
import ProductCoordinateExpansion_v1

/-! Recover equality of each genuine Y coefficient polynomial by comparing
finite spectator polynomials on real spectator values. In particular,
actual joint real circle invariance descends to each extracted Y polynomial;
complex polynomial invariance is not a premise. -/
set_option autoImplicit false
noncomputable section
namespace TheoremT.Continuum
open MvPolynomial WeakGrushin

def ksSpectatorEvaluationPolynomial (P : MvPolynomial (Fin 4 ⊕ Fin 3) ℂ)
    (y : Fin 4 → ℂ) : MvPolynomial (Fin 3) ℂ :=
  MvPolynomial.map (eval y) (ksSpectatorPolynomial P)

theorem ksSpectatorEvaluationPolynomial_coeff
    (P : MvPolynomial (Fin 4 ⊕ Fin 3) ℂ) (y : Fin 4 → ℂ) (γ : Fin 3 →₀ ℕ) :
    (ksSpectatorEvaluationPolynomial P y).coeff γ =
      eval y (ksSpectatorCoefficientPolynomial P γ) := by
  exact coeff_map (eval y) (ksSpectatorPolynomial P) γ

theorem ksSpectatorEvaluationPolynomial_eval
    (P : MvPolynomial (Fin 4 ⊕ Fin 3) ℂ) (y : Fin 4 → ℂ) (t : Fin 3 → ℂ) :
    eval t (ksSpectatorEvaluationPolynomial P y) = eval (Sum.elim y t) P := by
  unfold ksSpectatorEvaluationPolynomial
  rw [← eval₂_eq_eval_map,ksSpectatorPolynomial_eval]

theorem ksSpectatorCoefficientPolynomial_eval_eq_of_real_spectator_eq
    (P : MvPolynomial (Fin 4 ⊕ Fin 3) ℂ) (y z : Fin 4 → ℂ)
    (h : ∀ t : Fin 3 → ℝ,
      eval (Sum.elim y (fun i => (t i : ℂ))) P =
        eval (Sum.elim z (fun i => (t i : ℂ))) P) (γ : Fin 3 →₀ ℕ) :
    eval y (ksSpectatorCoefficientPolynomial P γ) =
      eval z (ksSpectatorCoefficientPolynomial P γ) := by
  have hp : ksSpectatorEvaluationPolynomial P y = ksSpectatorEvaluationPolynomial P z := by
    apply complexPolynomial_eq_of_real_eval_eq
    intro t
    simpa only [ksSpectatorEvaluationPolynomial_eval] using h t
  have hc := congrArg (fun Q : MvPolynomial (Fin 3) ℂ => Q.coeff γ) hp
  simpa only [ksSpectatorEvaluationPolynomial_coeff] using hc

theorem ksJointPolynomial_product_coordinate_eval
    (P : MvPolynomial (Fin 4 ⊕ Fin 3) ℂ) (q : Space (Fin 3)) :
    eval (fun j => (productCoordinateComponent q j : ℂ)) P =
      eval (Sum.elim (fun i => (q.1 i : ℂ)) (fun i => (q.2 i : ℂ))) P := by
  apply congrArg (fun f : Fin 4 ⊕ Fin 3 → ℂ => eval f P)
  funext i
  cases i <;> rfl

theorem ksSpectatorCoefficientPolynomial_circle_invariant
    (P : MvPolynomial (Fin 4 ⊕ Fin 3) ℂ) (a b : ℝ)
    (hJoint : ∀ q : Space (Fin 3),
      eval (fun j => (productCoordinateComponent (ksCircleProductCLM a b q) j : ℂ)) P =
        eval (fun j => (productCoordinateComponent q j : ℂ)) P)
    (γ : Fin 3 →₀ ℕ) (y : KSSpace) :
    eval (fun i => (ksCircleAction a b y i : ℂ)) (ksSpectatorCoefficientPolynomial P γ) =
      eval (fun i => (y i : ℂ)) (ksSpectatorCoefficientPolynomial P γ) := by
  apply ksSpectatorCoefficientPolynomial_eval_eq_of_real_spectator_eq
  intro t
  have h := hJoint (y,WithLp.toLp 2 t)
  simpa only [ksJointPolynomial_product_coordinate_eval,ksCircleProductCLM_apply] using h

theorem ksSpectatorCoefficientPolynomial_balanced_support
    (P : MvPolynomial (Fin 4 ⊕ Fin 3) ℂ)
    (hJoint : ∀ a b : ℝ, a^2+b^2=1 → ∀ q : Space (Fin 3),
      eval (fun j => (productCoordinateComponent (ksCircleProductCLM a b q) j : ℂ)) P =
        eval (fun j => (productCoordinateComponent q j : ℂ)) P)
    (γ : Fin 3 →₀ ℕ) :
    ∀ d ∈ (ksRealPolynomialToSpinor (ksSpectatorCoefficientPolynomial P γ)).support,
      d 0+d 1=d 2+d 3 := by
  apply ksRealPolynomialToSpinor_balanced_support
  intro a b h y
  exact ksSpectatorCoefficientPolynomial_circle_invariant P a b (hJoint a b h) γ y

end TheoremT.Continuum
