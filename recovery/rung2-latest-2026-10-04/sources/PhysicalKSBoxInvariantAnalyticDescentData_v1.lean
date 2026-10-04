import PhysicalKSBoxAnalyticDescentData_v2
import PhysicalKSAnalyticDescentRotation_v1

/-! The same physical A/B sums, analytic identity and mixed derivative bounds
are retained, together with literal invariance of both coefficients under
every orthogonal rotation fixing the actual spectator t0+T. -/
set_option autoImplicit false
noncomputable section
namespace TheoremT.Continuum
open WeakGrushin

def PhysicalKSBoxInvariantAnalyticDescentDerivativeData
    (f : Space (Fin 3) → ℂ) (v : Position → Position → ℂ)
    (t0 : Position) (M A F0 W : ℝ) : Prop :=
  PhysicalKSBoxAnalyticDescentDerivativeData f v t0 M A F0 W ∧
  ∀ (Q : Position ≃ₗᵢ[ℝ] Position) (T : Position),
    ‖T‖ < physicalKSPhysicalSpectatorRadius M A → Q (t0+T) = t0+T →
    ∀ X : Position, ‖X‖ < physicalKSPhysicalSpatialRadius M A →
      physicalKSAnalyticDescentA f t0
          (Sum.elim (fun j => (Q X j : ℂ)) (fun j => (T j : ℂ))) =
        physicalKSAnalyticDescentA f t0
          (Sum.elim (fun j => (X j : ℂ)) (fun j => (T j : ℂ))) ∧
      physicalKSAnalyticDescentB f t0
          (Sum.elim (fun j => (Q X j : ℂ)) (fun j => (T j : ℂ))) =
        physicalKSAnalyticDescentB f t0
          (Sum.elim (fun j => (X j : ℂ)) (fun j => (T j : ℂ)))

theorem nuclearKSPhysicalAnalyticDescent_invariant_derivative_data
    (g : Configuration 2 → ℂ) (i : Fin 2) {t0 : Position} {M A F0 W : ℝ}
    (hdata : PhysicalKSBoxPointwiseData
      ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm) t0 M A F0 W)
    (hA : 1≤A) (hF0 : 0≤F0)
    (hg : ∀ Q : Position ≃ₗᵢ[ℝ] Position, ∀ x, g (configurationRotation 2 Q x) = g x) :
    PhysicalKSBoxInvariantAnalyticDescentDerivativeData
      ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm)
      (fun X T => g (nuclearKSPhysicalCoordinates i X T)) t0 M A F0 W := by
  refine ⟨nuclearKSPhysicalAnalyticDescent_derivative_data g i hdata hA hF0, ?_⟩
  intro Q T hT hfix X hX
  exact nuclearKSPhysicalAnalyticDescent_rotation_invariant g i hdata hA hF0
    Q (hg Q) T hT hfix X hX

theorem pairKSPhysicalAnalyticDescent_invariant_derivative_data
    (g : Configuration 2 → ℂ) {t0 : Position} {M A F0 W : ℝ}
    (hdata : PhysicalKSBoxPointwiseData
      ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm) t0 M A F0 W)
    (hA : 1≤A) (hF0 : 0≤F0)
    (hg : ∀ Q : Position ≃ₗᵢ[ℝ] Position, ∀ x, g (configurationRotation 2 Q x) = g x) :
    PhysicalKSBoxInvariantAnalyticDescentDerivativeData
      ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm)
      (fun X T => g (pairKSPhysicalCoordinates X T)) t0 M A F0 W := by
  refine ⟨pairKSPhysicalAnalyticDescent_derivative_data g hdata hA hF0, ?_⟩
  intro Q T hT hfix X hX
  exact pairKSPhysicalAnalyticDescent_rotation_invariant g hdata hA hF0
    Q (hg Q) T hT hfix X hX

end TheoremT.Continuum
