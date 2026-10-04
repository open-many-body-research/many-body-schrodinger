import PhysicalKSAnalyticDescentIsometry_v1
import PhysicalKSCoordinatesRotation_v1

/-! Actual nuclear/pair A/B functions inherit the rotations fixing their
physical spectator. The only symmetry premise concerns the original
physical function; analytic regularity and the representation are derived
from actual pointwise chart data. -/
noncomputable section
set_option autoImplicit false
namespace TheoremT.Continuum

theorem nuclearKSPhysicalAnalyticDescent_rotation_invariant
    (g : Configuration 2 → ℂ) (i : Fin 2) {t0 : Position} {M A F0 W : ℝ}
    (hdata : PhysicalKSBoxPointwiseData ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm) t0 M A F0 W)
    (hA : 1≤A) (hF0 : 0≤F0)
    (R : Position ≃ₗᵢ[ℝ] Position)
    (hg : ∀ q : Configuration 2, g (configurationRotation 2 R q)=g q)
    (T : Position) (hT : ‖T‖<physicalKSPhysicalSpectatorRadius M A)
    (hfix : R (t0+T)=t0+T)
    (X : Position) (hX : ‖X‖<physicalKSPhysicalSpatialRadius M A) :
    physicalKSAnalyticDescentA ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm) t0
        (Sum.elim (fun j => (R X j : ℂ)) (fun j => (T j : ℂ))) =
      physicalKSAnalyticDescentA ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm) t0
        (Sum.elim (fun j => (X j : ℂ)) (fun j => (T j : ℂ))) ∧
    physicalKSAnalyticDescentB ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm) t0
        (Sum.elim (fun j => (R X j : ℂ)) (fun j => (T j : ℂ))) =
      physicalKSAnalyticDescentB ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm) t0
        (Sum.elim (fun j => (X j : ℂ)) (fun j => (T j : ℂ))) := by
  apply physicalKSAnalyticDescent_isometry_invariant_of_slice hA
    (nuclearKSPhysicalAnalyticDescent_physical_neighborhood g i hdata hA hF0) T hT
    (nuclearKSPhysicalAnalyticDescent_real_position_slices g i hdata hA hF0 T
      (physicalKSPhysicalSpectatorRadius_rate_bound hA T hT)) R _ X hX
  intro Y hY
  have h := hg (nuclearKSPhysicalCoordinates i Y (t0+T))
  rw [configurationRotation_nuclearKSPhysicalCoordinates R i Y (t0+T),hfix] at h
  exact h

theorem pairKSPhysicalAnalyticDescent_rotation_invariant
    (g : Configuration 2 → ℂ) {t0 : Position} {M A F0 W : ℝ}
    (hdata : PhysicalKSBoxPointwiseData ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm) t0 M A F0 W)
    (hA : 1≤A) (hF0 : 0≤F0)
    (R : Position ≃ₗᵢ[ℝ] Position)
    (hg : ∀ q : Configuration 2, g (configurationRotation 2 R q)=g q)
    (T : Position) (hT : ‖T‖<physicalKSPhysicalSpectatorRadius M A)
    (hfix : R (t0+T)=t0+T)
    (X : Position) (hX : ‖X‖<physicalKSPhysicalSpatialRadius M A) :
    physicalKSAnalyticDescentA ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm) t0
        (Sum.elim (fun j => (R X j : ℂ)) (fun j => (T j : ℂ))) =
      physicalKSAnalyticDescentA ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm) t0
        (Sum.elim (fun j => (X j : ℂ)) (fun j => (T j : ℂ))) ∧
    physicalKSAnalyticDescentB ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm) t0
        (Sum.elim (fun j => (R X j : ℂ)) (fun j => (T j : ℂ))) =
      physicalKSAnalyticDescentB ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm) t0
        (Sum.elim (fun j => (X j : ℂ)) (fun j => (T j : ℂ))) := by
  apply physicalKSAnalyticDescent_isometry_invariant_of_slice hA
    (pairKSPhysicalAnalyticDescent_physical_neighborhood g hdata hA hF0) T hT
    (pairKSPhysicalAnalyticDescent_real_position_slices g hdata hA hF0 T
      (physicalKSPhysicalSpectatorRadius_rate_bound hA T hT)) R _ X hX
  intro Y hY
  have h := hg (pairKSPhysicalCoordinates Y (t0+T))
  rw [configurationRotation_pairKSPhysicalCoordinates R Y (t0+T),hfix] at h
  exact h

end TheoremT.Continuum
