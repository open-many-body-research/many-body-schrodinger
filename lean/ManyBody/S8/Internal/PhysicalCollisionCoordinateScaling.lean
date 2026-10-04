import PhysicalSpectatorReindexAll_v1
import LocallyLipschitzScaledDifference_v1
import Mathlib.Tactic
/-! Genuine linear reconstruction of original physical collision coordinates.

Both maps are composed from the unchanged physical coordinate equivalences:
the selected nuclear configuration product and the restored coefficient-1
pair reconstruction. Their exact applications are proved by definition.
Linearity yields the literal normalized difference identity at any scale;
no replacement operator, graph transport, or Jacobian premise is introduced.
-/
noncomputable section
namespace ManyBody.S8
open TheoremT.Continuum

def originalNuclearPhysicalCoordinatesCLM (i : Fin 2) :
    (Position × Position) →L[ℝ] Configuration 2 :=
  (configurationProductEquiv i).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.id ℝ Position).prodMap
      (twoElectronSpectatorPositionEquiv i).symm.toContinuousLinearMap)

def originalPairPhysicalCoordinatesCLM : (Position × Position) →L[ℝ] Configuration 2 :=
  TheoremT.Continuum.pairCoordinates.comp
    ((ContinuousLinearMap.id ℝ Position).prodMap
      TheoremT.Continuum.pairCenterEquiv.symm.toContinuousLinearMap)

theorem originalNuclearPhysicalCoordinatesCLM_apply (i : Fin 2) (p : Position × Position) :
    originalNuclearPhysicalCoordinatesCLM i p =
      (configurationProductEquiv i).symm
        (p.1,(twoElectronSpectatorPositionEquiv i).symm p.2) := rfl

theorem originalPairPhysicalCoordinatesCLM_apply (p : Position × Position) :
    originalPairPhysicalCoordinatesCLM p =
      TheoremT.Continuum.pairCoordinates
        (p.1,TheoremT.Continuum.pairCenterEquiv.symm p.2) := rfl

theorem originScaledDifference_comp_physical_coordinates
    (g : Configuration 2 → ℂ) (C : (Position × Position) →L[ℝ] Configuration 2)
    (ε : ℝ) (p : Position × Position) :
    originScaledDifference g ε (C p) =
      (g (C (ε • p))-g (C 0))/(ε:ℂ) := by
  simp only [originScaledDifference,map_smul,map_zero,Complex.real_smul,
    Complex.ofReal_inv,div_eq_mul_inv]
  ring

#print axioms originalNuclearPhysicalCoordinatesCLM_apply
#print axioms originalPairPhysicalCoordinatesCLM_apply
#print axioms originScaledDifference_comp_physical_coordinates
end ManyBody.S8