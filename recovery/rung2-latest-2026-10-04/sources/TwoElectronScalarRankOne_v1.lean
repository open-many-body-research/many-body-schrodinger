import TwoElectronPhysicalRankOne_v1
import TwoElectronProjectionComparison_v1
import ScalarCoulombForm_v1

/-! Actual two-electron rank-one comparison on the unrestricted scalar H¹
space. No exchange symmetry is assumed in this scalar result. -/
noncomputable section
open MeasureTheory
namespace TheoremT.Continuum
open TheoremT.Polar

theorem twoElectron_scalar_h1_rank_one (Z : ℝ) (hZ : 0 < Z)
    {F : SpatialL2 2} {q : ℝ} (hq : scalarCoulombH1FormValue 2 Z F q) :
    -(5*Z^2/8) * ‖F‖^2 ≤ q + (3*Z^2/8) *
      ‖inner ℂ (twoElectronTensor
        (normalizedPolarGround configuration_one_finrank Z hZ)
        (normalizedPolarGround configuration_one_finrank Z hZ)) F‖^2 := by
  obtain ⟨d,v,hd,hv,rfl⟩ := hq
  apply twoElectron_scalar_comparison_of_component_bounds _ _
    (normalizedPolarGround_norm configuration_one_finrank Z hZ)
    (normalizedPolarGround_norm configuration_one_finrank Z hZ) F Z
    (twoElectronScalarComponentEnergy Z 0 F d) (twoElectronScalarComponentEnergy Z 1 F d)
  · have h := twoElectron_first_hydrogen_component Z hZ F d hd
    linarith
  · have h := twoElectron_second_hydrogen_component Z hZ F d hd
    linarith
  · unfold scalarCoulombH1Energy
    rw [← spatialL2_real_inner_eq_re]
    exact twoElectron_scalar_components_le_energy Z hZ.le F v d hd hv

#print axioms twoElectron_scalar_h1_rank_one
end TheoremT.Continuum
