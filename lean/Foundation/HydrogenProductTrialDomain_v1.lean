import TwoElectronTensorH2_v1
import TwoElectronFermionicJointProjection_v1
import NormalizedHydrogenGraph_v1
import CoulombDomainTotal_v2

/-! The literal normalized hydrogen product singlet lies in the actual Coulomb
H2 operator domain for every real nuclear charge and every positive trial scale.
This auxiliary trial does not redefine the frozen approximation dictionary. -/
noncomputable section
namespace TheoremT.Continuum
open TheoremT.Polar

theorem twoElectronRawSinglet_hasH2 {f : SpatialL2 1} (hf : HasH2 f)
    (σ : SpinConfiguration 2) : HasH2 (twoElectronRawSinglet f σ) := by
  rw [twoElectronRawSinglet_apply]
  have ht := twoElectronTensor_hasH2 hf hf
  have h1 : HasH2 (if σ = twoSpin01 then twoElectronTensor f f else 0) := by
    split_ifs <;> first | exact ht | exact hasH2_zero 2
  have h2 : HasH2 (if σ = twoSpin10 then twoElectronTensor f f else 0) := by
    split_ifs <;> first | exact ht | exact hasH2_zero 2
  exact (spatialH2Submodule 2).sub_mem h1 h2

theorem twoElectronSinglet_hasH2 {f : SpatialL2 1} (hf : HasH2 f)
    (σ : SpinConfiguration 2) : HasH2 (twoElectronSinglet f σ) := by
  change HasH2 (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • twoElectronRawSinglet f σ)
  exact (twoElectronRawSinglet_hasH2 hf σ).smul _

theorem twoElectronFermionicSinglet_mem_domain {f : SpatialL2 1} (hf : HasH2 f)
    (Z : ℝ) : twoElectronFermionicSinglet f ∈ (coulombPartialOperator 2 Z).domain := by
  apply (coulombPartialOperator_domain_iff_H2 2 Z _).mpr
  exact twoElectronSinglet_hasH2 hf

def hydrogenProductTrial (Z α : ℝ) (hα : 0 < α) : (coulombPartialOperator 2 Z).domain :=
  ⟨twoElectronFermionicSinglet (normalizedPolarGround configuration_one_finrank α hα),
    twoElectronFermionicSinglet_mem_domain (normalizedPolarGround_hasH2 α hα) Z⟩

theorem hydrogenProductTrial_norm (Z α : ℝ) (hα : 0 < α) :
    ‖(hydrogenProductTrial Z α hα : FermionicSpace 2)‖ = 1 :=
  twoElectronFermionicSinglet_norm _ (normalizedPolarGround_norm configuration_one_finrank α hα)

#print axioms twoElectronRawSinglet_hasH2
#print axioms twoElectronSinglet_hasH2
#print axioms twoElectronFermionicSinglet_mem_domain
#print axioms hydrogenProductTrial_norm
end TheoremT.Continuum
