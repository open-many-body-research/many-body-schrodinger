import PhysicalKSCoordinatesRotation_v1
import TwoElectronTensorExchange_v1
import PotentialPermutation_v2

/-! Exchange of the actual two electron positions negates the pair difference
X and leaves their center T unchanged. The normalized scaled difference
retains pointwise exchange invariance without a restriction on epsilon. -/
noncomputable section
set_option autoImplicit false
namespace TheoremT.Continuum

theorem permuteSpace_swap_pairKSPhysicalCoordinates (X T : Position) :
    permuteSpace twoElectronSwap (pairKSPhysicalCoordinates X T) =
      pairKSPhysicalCoordinates (-X) T := by
  ext ⟨j,k⟩
  change position (permuteSpace twoElectronSwap (pairKSPhysicalCoordinates X T)) j k =
    position (pairKSPhysicalCoordinates (-X) T) j k
  rw [position_permuteSpace]
  fin_cases j
  · change position (pairKSPhysicalCoordinates X T) 1 k =
      position (pairKSPhysicalCoordinates (-X) T) 0 k
    simp only [position_pairKSPhysicalCoordinates_one, position_pairKSPhysicalCoordinates_zero,
      smul_neg, sub_eq_add_neg]
  · change position (pairKSPhysicalCoordinates X T) 0 k =
      position (pairKSPhysicalCoordinates (-X) T) 1 k
    simp only [position_pairKSPhysicalCoordinates_zero, position_pairKSPhysicalCoordinates_one,
      smul_neg, sub_neg_eq_add]

theorem originScaledDifference_permuteSpace {N : ℕ}
    (g : Configuration N → ℂ) (π : Equiv.Perm (Fin N))
    (hg : ∀ x, g (permuteSpace π x) = g x) (ε : ℝ) (x : Configuration N) :
    originScaledDifference g ε (permuteSpace π x) = originScaledDifference g ε x := by
  unfold originScaledDifference
  rw [← (permuteSpace π).map_smul ε x,hg]

theorem originScaledDifference_pairKSPhysicalCoordinates_even
    (g : Configuration 2 → ℂ)
    (hg : ∀ x, g (permuteSpace twoElectronSwap x) = g x)
    (ε : ℝ) (X T : Position) :
    originScaledDifference g ε (pairKSPhysicalCoordinates (-X) T) =
      originScaledDifference g ε (pairKSPhysicalCoordinates X T) := by
  rw [← permuteSpace_swap_pairKSPhysicalCoordinates]
  exact originScaledDifference_permuteSpace g twoElectronSwap hg ε _

end TheoremT.Continuum
