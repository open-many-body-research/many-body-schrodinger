import PhysicalKSAnalyticDescentSurjectivity_v1
import ConfigurationRotation_v1

/-! Exact covariance of the actual nuclear and pair physical coordinates.
Every real linear isometric equivalence is allowed, including reflections.
The scaled-difference conclusions require literal pointwise invariance of
the input function and retain the original epsilon-inverse normalization. -/
noncomputable section
set_option autoImplicit false
namespace TheoremT.Continuum

theorem position_nuclearKSPhysicalCoordinates (i j : Fin 2) (X T : Position) :
    position (nuclearKSPhysicalCoordinates i X T) j = if j=i then X else T := by
  change position (configurationReassemble i X ((twoElectronSpectatorPositionEquiv i).symm T)) j = _
  by_cases h : j=i
  · subst j
    rw [if_pos rfl, configurationReassemble_position]
  · rw [if_neg h]
    ext k
    change configurationReassemble i X ((twoElectronSpectatorPositionEquiv i).symm T) (j,k) = T k
    rw [configurationReassemble_spectator i X _ (⟨(j,k),h⟩ : SpectatorCoordinate i),
      twoElectronSpectatorPositionEquiv_symm_apply]

theorem position_pairKSPhysicalCoordinates_zero (X T : Position) :
    position (pairKSPhysicalCoordinates X T) 0 = T + (1/2 : ℝ) • X := by
  rw [pairKSPhysicalCoordinates,pairCoordinates_first,pairCenterEquiv.apply_symm_apply]

theorem position_pairKSPhysicalCoordinates_one (X T : Position) :
    position (pairKSPhysicalCoordinates X T) 1 = T - (1/2 : ℝ) • X := by
  rw [pairKSPhysicalCoordinates,pairCoordinates_second,pairCenterEquiv.apply_symm_apply]

theorem configurationRotation_nuclearKSPhysicalCoordinates
    (R : Position ≃ₗᵢ[ℝ] Position) (i : Fin 2) (X T : Position) :
    configurationRotation 2 R (nuclearKSPhysicalCoordinates i X T) =
      nuclearKSPhysicalCoordinates i (R X) (R T) := by
  ext ⟨j,k⟩
  change position (configurationRotation 2 R (nuclearKSPhysicalCoordinates i X T)) j k =
    position (nuclearKSPhysicalCoordinates i (R X) (R T)) j k
  rw [position_configurationRotation,position_nuclearKSPhysicalCoordinates,
    position_nuclearKSPhysicalCoordinates]
  split_ifs <;> rfl

theorem configurationRotation_pairKSPhysicalCoordinates
    (R : Position ≃ₗᵢ[ℝ] Position) (X T : Position) :
    configurationRotation 2 R (pairKSPhysicalCoordinates X T) =
      pairKSPhysicalCoordinates (R X) (R T) := by
  ext ⟨j,k⟩
  change position (configurationRotation 2 R (pairKSPhysicalCoordinates X T)) j k =
    position (pairKSPhysicalCoordinates (R X) (R T)) j k
  rw [position_configurationRotation]
  fin_cases j
  · change (R (position (pairKSPhysicalCoordinates X T) 0)) k =
      position (pairKSPhysicalCoordinates (R X) (R T)) 0 k
    rw [position_pairKSPhysicalCoordinates_zero,position_pairKSPhysicalCoordinates_zero,
      map_add,map_smul]
  · change (R (position (pairKSPhysicalCoordinates X T) 1)) k =
      position (pairKSPhysicalCoordinates (R X) (R T)) 1 k
    rw [position_pairKSPhysicalCoordinates_one,position_pairKSPhysicalCoordinates_one,
      map_sub,map_smul]

theorem originScaledDifference_configurationRotation {N : ℕ}
    (g : Configuration N → ℂ) (R : Position ≃ₗᵢ[ℝ] Position)
    (hg : ∀ x, g (configurationRotation N R x) = g x) (ε : ℝ) (x : Configuration N) :
    originScaledDifference g ε (configurationRotation N R x) = originScaledDifference g ε x := by
  unfold originScaledDifference
  rw [← (configurationRotation N R).map_smul ε x,hg]

theorem originScaledDifference_nuclearKSPhysicalCoordinates_rotation
    (g : Configuration 2 → ℂ) (R : Position ≃ₗᵢ[ℝ] Position)
    (hg : ∀ x, g (configurationRotation 2 R x) = g x)
    (ε : ℝ) (i : Fin 2) (X T : Position) :
    originScaledDifference g ε (nuclearKSPhysicalCoordinates i (R X) (R T)) =
      originScaledDifference g ε (nuclearKSPhysicalCoordinates i X T) := by
  rw [← configurationRotation_nuclearKSPhysicalCoordinates]
  exact originScaledDifference_configurationRotation g R hg ε _

theorem originScaledDifference_pairKSPhysicalCoordinates_rotation
    (g : Configuration 2 → ℂ) (R : Position ≃ₗᵢ[ℝ] Position)
    (hg : ∀ x, g (configurationRotation 2 R x) = g x)
    (ε : ℝ) (X T : Position) :
    originScaledDifference g ε (pairKSPhysicalCoordinates (R X) (R T)) =
      originScaledDifference g ε (pairKSPhysicalCoordinates X T) := by
  rw [← configurationRotation_pairKSPhysicalCoordinates]
  exact originScaledDifference_configurationRotation g R hg ε _

end TheoremT.Continuum
