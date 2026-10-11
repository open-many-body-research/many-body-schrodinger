import PhysicalKSAnalyticDescentIsometry_v1
import PhysicalKSPairExchange_v1

/-! The actual pair A/B coefficients are even in the pair difference X
when the physical input is invariant under electron exchange. This uses
exchange, not an assumption that negation fixes the nonzero spectator. -/
noncomputable section
set_option autoImplicit false
namespace TheoremT.Continuum

theorem pairKSPhysicalAnalyticDescent_even
    (g : Configuration 2 → ℂ) {t0 : Position} {M A F0 W : ℝ}
    (hdata : PhysicalKSBoxPointwiseData
      ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm) t0 M A F0 W)
    (hA : 1≤A) (hF0 : 0≤F0)
    (hg : ∀ x, g (permuteSpace twoElectronSwap x) = g x)
    (T : Position) (hT : ‖T‖ < physicalKSPhysicalSpectatorRadius M A)
    (X : Position) (hX : ‖X‖ < physicalKSPhysicalSpatialRadius M A) :
    physicalKSAnalyticDescentA
        ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm) t0
        (Sum.elim (fun j => ((-X) j : ℂ)) (fun j => (T j : ℂ))) =
      physicalKSAnalyticDescentA
        ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm) t0
        (Sum.elim (fun j => (X j : ℂ)) (fun j => (T j : ℂ))) ∧
    physicalKSAnalyticDescentB
        ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm) t0
        (Sum.elim (fun j => ((-X) j : ℂ)) (fun j => (T j : ℂ))) =
      physicalKSAnalyticDescentB
        ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm) t0
        (Sum.elim (fun j => (X j : ℂ)) (fun j => (T j : ℂ))) := by
  apply physicalKSAnalyticDescent_isometry_invariant_of_slice hA
    (pairKSPhysicalAnalyticDescent_physical_neighborhood g hdata hA hF0) T hT
    (pairKSPhysicalAnalyticDescent_real_position_slices g hdata hA hF0 T
      (physicalKSPhysicalSpectatorRadius_rate_bound hA T hT))
    (LinearIsometryEquiv.neg ℝ) _ X hX
  intro Y hY
  have h := hg (pairKSPhysicalCoordinates Y (t0+T))
  rw [permuteSpace_swap_pairKSPhysicalCoordinates] at h
  exact h

end TheoremT.Continuum
