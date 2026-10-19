import PhysicalKSBoxInvariantAnalyticDescentData_v1
import PhysicalKSPairAnalyticDescentEven_v1

/-! The invariant analytic derivative data is retained together with literal
evenness of both A/B coefficients in X. The pair constructor derives this
extra clause from physical electron-exchange symmetry. -/
noncomputable section
set_option autoImplicit false
namespace TheoremT.Continuum
open WeakGrushin

def PhysicalKSBoxEvenInvariantAnalyticDescentDerivativeData
    (f : Space (Fin 3) → ℂ) (v : Position → Position → ℂ)
    (t0 : Position) (M A F0 W : ℝ) : Prop :=
  PhysicalKSBoxInvariantAnalyticDescentDerivativeData f v t0 M A F0 W ∧
  ∀ T : Position, ‖T‖ < physicalKSPhysicalSpectatorRadius M A →
    ∀ X : Position, ‖X‖ < physicalKSPhysicalSpatialRadius M A →
      physicalKSAnalyticDescentA f t0
          (Sum.elim (fun j => ((-X) j : ℂ)) (fun j => (T j : ℂ))) =
        physicalKSAnalyticDescentA f t0
          (Sum.elim (fun j => (X j : ℂ)) (fun j => (T j : ℂ))) ∧
      physicalKSAnalyticDescentB f t0
          (Sum.elim (fun j => ((-X) j : ℂ)) (fun j => (T j : ℂ))) =
        physicalKSAnalyticDescentB f t0
          (Sum.elim (fun j => (X j : ℂ)) (fun j => (T j : ℂ)))

theorem pairKSPhysicalAnalyticDescent_even_invariant_derivative_data
    (g : Configuration 2 → ℂ) {t0 : Position} {M A F0 W : ℝ}
    (hdata : PhysicalKSBoxPointwiseData
      ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm) t0 M A F0 W)
    (hA : 1≤A) (hF0 : 0≤F0)
    (hrotation : ∀ Q : Position ≃ₗᵢ[ℝ] Position, ∀ x,
      g (configurationRotation 2 Q x) = g x)
    (hexchange : ∀ x, g (permuteSpace twoElectronSwap x) = g x) :
    PhysicalKSBoxEvenInvariantAnalyticDescentDerivativeData
      ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm)
      (fun X T => g (pairKSPhysicalCoordinates X T)) t0 M A F0 W := by
  refine ⟨pairKSPhysicalAnalyticDescent_invariant_derivative_data g hdata hA hF0 hrotation, ?_⟩
  intro T hT X hX
  exact pairKSPhysicalAnalyticDescent_even g hdata hA hF0 hexchange T hT X hX

end TheoremT.Continuum
