import PolarMeanVariance_v1
import NormalizedMeanIntegrability_v1
import PolarMassCoulombMarginals_v1

/-! Actual mass, nuclear, and radial kinetic mean/fluctuation decompositions.
Every integral is justified by compact support and the actual half-line mean
domain; no variance or integrability premise is left to the caller. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ContDiff Topology
namespace TheoremT.Polar

theorem physical_mean_fluctuation_mass_integral {f : EnergyR3 → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (h0 : (0 : EnergyR3) ∉ tsupport f) :
    (∫ x : EnergyR3, ‖f x‖ ^ 2) =
      (4 * Real.pi) * (∫ r : ℝ in Ioi 0, r ^ 2 * ‖normalizedRadialMean f r‖ ^ 2) +
      (∫ x : EnergyR3, ‖physicalFluctuation f x‖ ^ 2) := by
  have hF := physicalFluctuation_contDiff hf h0
  have hFc := physicalFluctuation_compact hc
  have hm := MeanProfile.mean_mass_integrable f hf hc h0
  have hg := compact_mass_radius_marginal_integrable hF.continuous hFc
  rw [compact_mass_polar_radius_outer hf.continuous hc,
    compact_mass_polar_radius_outer hF.continuous hFc]
  calc
    _ = ∫ r : ℝ in Ioi 0, ((4 * Real.pi) * (r ^ 2 * ‖normalizedRadialMean f r‖ ^ 2) +
        r ^ 2 * (∫ w : EnergySphere, ‖physicalFluctuation f (r • w.val)‖ ^ 2
          ∂(volume : Measure EnergyR3).toSphere)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      dsimp only
      rw [physical_mean_fluctuation_sphere_mass hf.continuous (le_of_lt hr)]
      ring
    _ = _ := by rw [integral_add (hm.const_mul (4 * Real.pi)) hg, integral_const_mul]

theorem physical_mean_fluctuation_nuclear_integral {f : EnergyR3 → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (h0 : (0 : EnergyR3) ∉ tsupport f) :
    (∫ x : EnergyR3, ‖f x‖ ^ 2 / ‖x‖) =
      (4 * Real.pi) * (∫ r : ℝ in Ioi 0, r * ‖normalizedRadialMean f r‖ ^ 2) +
      (∫ x : EnergyR3, ‖physicalFluctuation f x‖ ^ 2 / ‖x‖) := by
  have hF := physicalFluctuation_contDiff hf h0
  have hFc := physicalFluctuation_compact hc
  have hF0 := physicalFluctuation_zero_not_tsupport h0
  have hm := MeanProfile.mean_nuclear_integrable f hf hc h0
  have hg := compact_coulomb_radius_marginal_integrable hF.continuous hFc hF0
  rw [compact_coulomb_polar_radius_outer hf.continuous hc h0,
    compact_coulomb_polar_radius_outer hF.continuous hFc hF0]
  calc
    _ = ∫ r : ℝ in Ioi 0, ((4 * Real.pi) * (r * ‖normalizedRadialMean f r‖ ^ 2) +
        r * (∫ w : EnergySphere, ‖physicalFluctuation f (r • w.val)‖ ^ 2
          ∂(volume : Measure EnergyR3).toSphere)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      dsimp only
      rw [physical_mean_fluctuation_sphere_mass hf.continuous (le_of_lt hr)]
      ring
    _ = _ := by rw [integral_add (hm.const_mul (4 * Real.pi)) hg, integral_const_mul]

theorem physical_mean_fluctuation_radial_kinetic_integral {f : EnergyR3 → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (h0 : (0 : EnergyR3) ∉ tsupport f) :
    (∫ r : ℝ in Ioi 0, r ^ 2 * (∫ w : EnergySphere,
      ‖fderiv ℝ f (r • w.val) w.val‖ ^ 2 ∂(volume : Measure EnergyR3).toSphere)) =
      (4 * Real.pi) * (∫ r : ℝ in Ioi 0, r ^ 2 * ‖normalizedRadialDerivativeMean f r‖ ^ 2) +
      (∫ r : ℝ in Ioi 0, r ^ 2 * (∫ w : EnergySphere,
        ‖fderiv ℝ (physicalFluctuation f) (r • w.val) w.val‖ ^ 2
          ∂(volume : Measure EnergyR3).toSphere)) := by
  have hF := physicalFluctuation_contDiff hf h0
  have hFc := physicalFluctuation_compact hc
  have hm := MeanProfile.mean_radial_kinetic_integrable f hf hc h0
  have hg := polarRadialEnergy_integrable hF hFc
  dsimp only [polarRadialDensity] at hg
  calc
    _ = ∫ r : ℝ in Ioi 0, ((4 * Real.pi) * (r ^ 2 * ‖normalizedRadialDerivativeMean f r‖ ^ 2) +
        r ^ 2 * (∫ w : EnergySphere,
          ‖fderiv ℝ (physicalFluctuation f) (r • w.val) w.val‖ ^ 2
            ∂(volume : Measure EnergyR3).toSphere)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      dsimp only
      rw [physical_mean_fluctuation_sphere_radial_kinetic hf h0 hr]
      ring
    _ = _ := by rw [integral_add (hm.const_mul (4 * Real.pi)) hg, integral_const_mul]

end TheoremT.Polar
