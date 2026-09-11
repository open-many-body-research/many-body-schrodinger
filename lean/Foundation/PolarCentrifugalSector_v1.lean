import PolarCentrifugalIntegrated_v1
import PolarFullEnergy_v1

/-! Conditional composition of the actual radial centrifugal and angular
bounds. The sole remaining angular premise is printed explicitly as the
actual per-radius sphere inequality; it is not a hydrogen-energy premise. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ContDiff Topology
namespace TheoremT.Polar

theorem inverseSquare_le_half_angular_of_sphere_bound {f : EnergyR3 → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (h0 : (0 : EnergyR3) ∉ tsupport f)
    (hangular : ∀ r : ℝ, 0 < r →
      2 * (∫ w : EnergySphere, ‖f (r • w.val)‖ ^ 2 ∂(volume : Measure EnergyR3).toSphere) ≤
      ∑ i : Fin 3, ∫ w : EnergySphere,
        ‖complexTangentialPartial i (fun y => f (r • y)) w.val‖ ^ 2
          ∂(volume : Measure EnergyR3).toSphere) :
    (∫ x : EnergyR3, ‖f x‖ ^ 2 / ‖x‖ ^ 2) ≤
      (1 / 2) * ∑ i : Fin 3, ∫ r : ℝ in Ioi 0, ∫ w : EnergySphere,
        ‖complexTangentialPartial i (fun y => f (r • y)) w.val‖ ^ 2
          ∂(volume : Measure EnergyR3).toSphere := by
  have hi := compact_inverseSquare_radius_marginal_integrable hf.continuous hc h0
  have ht := integrable_finsetSum Finset.univ
    (fun i _ => scaled_tangential_radial_integrable hf hc i)
  have hle := integral_mono_ae (hi.const_mul 2) ht (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact hangular r hr)
  rw [integral_const_mul,
    integral_finsetSum Finset.univ (fun i _ => scaled_tangential_radial_integrable hf hc i),
    ← compact_inverseSquare_polar_radius_outer hf.continuous hc h0] at hle
  linarith

theorem centrifugal_sector_lower_of_sphere_bound {f : EnergyR3 → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (h0 : (0 : EnergyR3) ∉ tsupport f)
    (Z : ℝ)
    (hangular : ∀ r : ℝ, 0 < r →
      2 * (∫ w : EnergySphere, ‖f (r • w.val)‖ ^ 2 ∂(volume : Measure EnergyR3).toSphere) ≤
      ∑ i : Fin 3, ∫ w : EnergySphere,
        ‖complexTangentialPartial i (fun y => f (r • y)) w.val‖ ^ 2
          ∂(volume : Measure EnergyR3).toSphere) :
    -(Z ^ 2 / 8) * (∫ x : EnergyR3, ‖f x‖ ^ 2) ≤
      (1 / 2) * (∫ x : EnergyR3, ∑ i : Fin 3,
        ‖fderiv ℝ f x (EuclideanSpace.single i 1)‖ ^ 2) -
      Z * (∫ x : EnergyR3, ‖f x‖ ^ 2 / ‖x‖) := by
  have hr := centrifugal_integrated_lower hf hc h0 Z
  have ha := inverseSquare_le_half_angular_of_sphere_bound hf hc h0 hangular
  rw [full_kinetic_polar_integral_separated hf hc]
  linarith

end TheoremT.Polar
