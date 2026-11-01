import SO2SpectatorCoefficientPolynomial_v1
import SO2PolynomialRealRotation_v1
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-! Literal planar rotation on the first two coordinates and identity on
spectator coordinates. Real invariance of a joint polynomial descends
to each genuine spectator coefficient polynomial by finite polynomial
identity, without assuming coefficient invariance. The finite extraction
argument adapts the immutable KSSpectatorCoefficientInvariance_v1. -/
noncomputable section
set_option autoImplicit false
namespace TheoremT.Continuum
open MvPolynomial

def so2JointRealRotationCLM (a b : ℝ) :
    (Fin 2 ⊕ Fin 2 → ℝ) →L[ℝ] (Fin 2 ⊕ Fin 2 → ℝ) :=
  ContinuousLinearMap.pi (Sum.elim
    ![a • ContinuousLinearMap.proj (Sum.inl 0) - b • ContinuousLinearMap.proj (Sum.inl 1),
      b • ContinuousLinearMap.proj (Sum.inl 0) + a • ContinuousLinearMap.proj (Sum.inl 1)]
    (fun i => ContinuousLinearMap.proj (Sum.inr i)))

theorem so2JointRealRotationCLM_apply (a b : ℝ) (z : Fin 2 ⊕ Fin 2 → ℝ) :
    so2JointRealRotationCLM a b z =
      Sum.elim (so2RealRotation a b (fun i => z (Sum.inl i)))
        (fun i => z (Sum.inr i)) := by
  ext i
  cases i with
  | inl j => fin_cases j <;> rfl
  | inr j => rfl

def so2SpectatorEvaluationPolynomial (P : MvPolynomial (Fin 2 ⊕ Fin 2) ℂ)
    (y : Fin 2 → ℂ) : MvPolynomial (Fin 2) ℂ :=
  MvPolynomial.map (eval y) (so2SpectatorPolynomial P)

theorem so2SpectatorEvaluationPolynomial_coeff
    (P : MvPolynomial (Fin 2 ⊕ Fin 2) ℂ) (y : Fin 2 → ℂ) (γ : Fin 2 →₀ ℕ) :
    (so2SpectatorEvaluationPolynomial P y).coeff γ =
      eval y (so2SpectatorCoefficientPolynomial P γ) := by
  exact coeff_map (eval y) (so2SpectatorPolynomial P) γ

theorem so2SpectatorEvaluationPolynomial_eval
    (P : MvPolynomial (Fin 2 ⊕ Fin 2) ℂ) (y : Fin 2 → ℂ) (t : Fin 2 → ℂ) :
    eval t (so2SpectatorEvaluationPolynomial P y) = eval (Sum.elim y t) P := by
  unfold so2SpectatorEvaluationPolynomial
  rw [← eval₂_eq_eval_map,so2SpectatorPolynomial_eval]

theorem so2SpectatorCoefficientPolynomial_eval_eq_of_real_spectator_eq
    (P : MvPolynomial (Fin 2 ⊕ Fin 2) ℂ) (y z : Fin 2 → ℂ)
    (h : ∀ t : Fin 2 → ℝ,
      eval (Sum.elim y (fun i => (t i : ℂ))) P =
        eval (Sum.elim z (fun i => (t i : ℂ))) P) (γ : Fin 2 →₀ ℕ) :
    eval y (so2SpectatorCoefficientPolynomial P γ) =
      eval z (so2SpectatorCoefficientPolynomial P γ) := by
  have hp : so2SpectatorEvaluationPolynomial P y = so2SpectatorEvaluationPolynomial P z := by
    apply complexPolynomial_eq_of_real_eval_eq
    intro t
    simpa only [so2SpectatorEvaluationPolynomial_eval] using h t
  have hc := congrArg (fun Q : MvPolynomial (Fin 2) ℂ => Q.coeff γ) hp
  simpa only [so2SpectatorEvaluationPolynomial_coeff] using hc

theorem so2SpectatorCoefficientPolynomial_rotation_invariant
    (P : MvPolynomial (Fin 2 ⊕ Fin 2) ℂ) (a b : ℝ)
    (hJoint : ∀ z : Fin 2 ⊕ Fin 2 → ℝ,
      eval (fun i => (so2JointRealRotationCLM a b z i : ℂ)) P =
        eval (fun i => (z i : ℂ)) P)
    (γ : Fin 2 →₀ ℕ) (y : Fin 2 → ℝ) :
    eval (fun i => (so2RealRotation a b y i : ℂ)) (so2SpectatorCoefficientPolynomial P γ) =
      eval (fun i => (y i : ℂ)) (so2SpectatorCoefficientPolynomial P γ) := by
  apply so2SpectatorCoefficientPolynomial_eval_eq_of_real_spectator_eq
  intro t
  have h := hJoint (Sum.elim y t)
  have he (v w : Fin 2 → ℝ) :
      (fun i => ((Sum.elim v w i : ℝ) : ℂ)) = Sum.elim (fun i => (v i : ℂ)) (fun i => (w i : ℂ)) := by
    funext i
    cases i <;> rfl
  simpa only [so2JointRealRotationCLM_apply,Sum.elim_inl,Sum.elim_inr,he] using h

theorem so2SpectatorCoefficientPolynomial_balanced_support
    (P : MvPolynomial (Fin 2 ⊕ Fin 2) ℂ)
    (hJoint : ∀ a b : ℝ, a^2+b^2=1 → ∀ z : Fin 2 ⊕ Fin 2 → ℝ,
      eval (fun i => (so2JointRealRotationCLM a b z i : ℂ)) P =
        eval (fun i => (z i : ℂ)) P)
    (γ : Fin 2 →₀ ℕ) :
    ∀ d ∈ (so2PolynomialToBalanced (so2SpectatorCoefficientPolynomial P γ)).support,
      d 0=d 1 := by
  apply so2PolynomialToBalanced_balanced_support_of_real_rotation
  intro a b hab y
  exact so2SpectatorCoefficientPolynomial_rotation_invariant P a b (hJoint a b hab) γ y

end TheoremT.Continuum
