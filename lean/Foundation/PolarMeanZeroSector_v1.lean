import PolarCentrifugalSector_v1
import ComplexSpherePoincare_v1
import PhysicalRadialMean_v1

/-! Actual hydrogenic lower bound for the zero spherical-mean sector. The
angular premise of the earlier conditional composition is discharged by the
proved complex sphere Poincare theorem. In particular, the actual fluctuation
of every punctured smooth compact input satisfies the bound. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ContDiff Topology
namespace TheoremT.Polar

theorem mean_zero_sector_energy_lower {f : EnergyR3 → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (h0 : (0 : EnergyR3) ∉ tsupport f)
    (Z : ℝ)
    (hm : ∀ r : ℝ, 0 < r →
      (∫ w : EnergySphere, f (r • w.val) ∂(volume : Measure EnergyR3).toSphere) = 0) :
    -(Z ^ 2 / 8) * (∫ x : EnergyR3, ‖f x‖ ^ 2) ≤
      (1 / 2) * (∫ x : EnergyR3, ∑ i : Fin 3,
        ‖fderiv ℝ f x (EuclideanSpace.single i 1)‖ ^ 2) -
      Z * (∫ x : EnergyR3, ‖f x‖ ^ 2 / ‖x‖) := by
  apply centrifugal_sector_lower_of_sphere_bound hf hc h0 Z
  intro r hr
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by simp)
  have hs : ContDiff ℝ 1 (fun y : EnergyR3 => f (r • y)) :=
    hf1.comp (contDiff_const_smul r)
  exact complex_sphere_poincare_mean_zero hs (hm r hr)

theorem physicalFluctuation_energy_lower {f : EnergyR3 → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (h0 : (0 : EnergyR3) ∉ tsupport f)
    (Z : ℝ) :
    -(Z ^ 2 / 8) * (∫ x : EnergyR3, ‖physicalFluctuation f x‖ ^ 2) ≤
      (1 / 2) * (∫ x : EnergyR3, ∑ i : Fin 3,
        ‖fderiv ℝ (physicalFluctuation f) x (EuclideanSpace.single i 1)‖ ^ 2) -
      Z * (∫ x : EnergyR3, ‖physicalFluctuation f x‖ ^ 2 / ‖x‖) := by
  apply mean_zero_sector_energy_lower (physicalFluctuation_contDiff hf h0)
    (physicalFluctuation_compact hc) (physicalFluctuation_zero_not_tsupport h0) Z
  intro r hr
  exact physicalFluctuation_sphere_mean_zero (by simp) hf.continuous hr.le

end TheoremT.Polar
