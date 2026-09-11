import OneElectronL2Transport_v1
import PolarGroundNormalization_v1

/-! The transported comparison vector is exactly the normalized physical
exp(-Z|x|) L2 class in the original Configuration 1 volume. -/
noncomputable section
open MeasureTheory Filter
namespace TheoremT.Continuum
open TheoremT.Polar TheoremT.HydrogenPolynomial

theorem oneElectronL2_ground (Z : ℝ) (hZ : 0 < Z) :
    oneElectronL2ToEuclidean (polarGroundL2 configuration_one_finrank Z hZ) =
      polarGroundL2 (by simp : Module.finrank ℝ AngularR3 = 3) Z hZ := by
  apply Lp.ext
  filter_upwards [oneElectronL2ToEuclidean_representative
    (polarGroundL2_coe configuration_one_finrank Z hZ),
    polarGroundL2_coe (by simp : Module.finrank ℝ AngularR3 = 3) Z hZ] with x hx hy
  rw [hx,hy]
  simp only [polarGroundFunction, LinearIsometryEquiv.norm_map]

theorem oneElectronL2_normalized_ground (Z : ℝ) (hZ : 0 < Z) :
    oneElectronL2ToEuclidean (normalizedPolarGround configuration_one_finrank Z hZ) =
      normalizedPolarGround (by simp : Module.finrank ℝ AngularR3 = 3) Z hZ := by
  have hn : ‖polarGroundL2 configuration_one_finrank Z hZ‖ =
      ‖polarGroundL2 (by simp : Module.finrank ℝ AngularR3 = 3) Z hZ‖ := by
    rw [← oneElectronL2_ground Z hZ, oneElectronL2ToEuclidean.norm_map]
  simp only [normalizedPolarGround, map_smul, oneElectronL2_ground Z hZ, hn]

theorem oneElectronL2_ground_inner (Z : ℝ) (hZ : 0 < Z) (g : SpatialL2 1) :
    inner ℂ (normalizedPolarGround (by simp : Module.finrank ℝ AngularR3 = 3) Z hZ)
      (oneElectronL2ToEuclidean g) =
    inner ℂ (normalizedPolarGround configuration_one_finrank Z hZ) g := by
  rw [← oneElectronL2_normalized_ground Z hZ]
  exact oneElectronL2ToEuclidean.inner_map_map _ _

theorem spatialL2_norm_sq_representative (g : SpatialL2 1)
    (u : Configuration 1 → ℂ) (hu : g =ᵐ[volume] u) :
    ‖g‖^2 = ∫ x, ‖u x‖^2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hu] with x hx
  rw [hx, real_inner_self_eq_norm_sq]

#print axioms oneElectronL2_ground
#print axioms oneElectronL2_normalized_ground
#print axioms oneElectronL2_ground_inner
#print axioms spatialL2_norm_sq_representative
end TheoremT.Continuum
