import OneElectronGroundTransport_v1
import HydrogenEigenGraph_v1
import ScalarCoulombOperator_v1

/-! The normalized comparison vector is the actual physical H2 hydrogen
eigenfunction. This identifies the exact weak graph, not a selected surrogate. -/
noncomputable section
open MeasureTheory Filter
namespace TheoremT.Continuum
open TheoremT.Polar

theorem polarGroundL2_eq_hydrogen (Z : ℝ) (hZ : 0 < Z) :
    polarGroundL2 configuration_one_finrank Z hZ = hydrogenRadialL2 Z hZ := by
  apply Lp.ext
  filter_upwards [polarGroundL2_coe configuration_one_finrank Z hZ,
    hydrogenRadialL2_coe_ae Z hZ] with x hx hy
  rw [hx,hy]
  rfl

theorem normalizedPolarGround_hasH2 (Z : ℝ) (hZ : 0 < Z) :
    HasH2 (normalizedPolarGround configuration_one_finrank Z hZ) := by
  rw [normalizedPolarGround, polarGroundL2_eq_hydrogen]
  exact (hydrogenRadialL2_hasH2 hZ).smul _

theorem normalizedPolarGround_eigenGraph (Z : ℝ) (hZ : 0 < Z) :
    scalarHamiltonianGraph 1 Z (normalizedPolarGround configuration_one_finrank Z hZ)
      ((-(Z^2/2) : ℂ) • normalizedPolarGround configuration_one_finrank Z hZ) := by
  rw [normalizedPolarGround, polarGroundL2_eq_hydrogen]
  have h := scalar_graph_smul (‖hydrogenRadialL2 Z hZ‖⁻¹ : ℂ)
    (hydrogenRadialL2_eigenGraph Z hZ)
  rw [smul_comm (‖hydrogenRadialL2 Z hZ‖⁻¹ : ℂ) (-(Z^2/2) : ℂ)] at h
  exact h

#print axioms polarGroundL2_eq_hydrogen
#print axioms normalizedPolarGround_hasH2
#print axioms normalizedPolarGround_eigenGraph
end TheoremT.Continuum
