import PolarFullEnergy_v1
import PhysicalRadialDerivative_v1

/-! Exact pointwise sphere variances for the actual physical mean/fluctuation
functions, both for their values and their actual radial derivatives. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ContDiff Topology
namespace TheoremT.Polar

theorem physical_mean_fluctuation_sphere_mass {f : EnergyR3 → ℂ}
    (hf : Continuous f) {r : ℝ} (hr : 0 ≤ r) :
    (∫ w : EnergySphere, ‖f (r • w.val)‖ ^ 2 ∂(volume : Measure EnergyR3).toSphere) =
      (4 * Real.pi) * ‖normalizedRadialMean f r‖ ^ 2 +
      (∫ w : EnergySphere, ‖physicalFluctuation f (r • w.val)‖ ^ 2
        ∂(volume : Measure EnergyR3).toSphere) := by
  simp_rw [physicalFluctuation_on_ray f _ hr]
  have h := radial_fluctuation_variance (by simp : Module.finrank ℝ EnergyR3 = 3) hf r
  dsimp only [sphereMeasure] at h
  linarith

theorem physical_mean_fluctuation_sphere_radial_kinetic {f : EnergyR3 → ℂ}
    (hf : ContDiff ℝ ∞ f) (h0 : (0 : EnergyR3) ∉ tsupport f) {r : ℝ} (hr : 0 < r) :
    (∫ w : EnergySphere, ‖fderiv ℝ f (r • w.val) w.val‖ ^ 2
      ∂(volume : Measure EnergyR3).toSphere) =
      (4 * Real.pi) * ‖normalizedRadialDerivativeMean f r‖ ^ 2 +
      (∫ w : EnergySphere, ‖fderiv ℝ (physicalFluctuation f) (r • w.val) w.val‖ ^ 2
        ∂(volume : Measure EnergyR3).toSphere) := by
  simp_rw [physicalFluctuation_radial_fderiv hf h0 _ hr]
  have h := radial_derivative_fluctuation_variance
    (by simp : Module.finrank ℝ EnergyR3 = 3) hf r
  dsimp only [sphereMeasure] at h
  linarith

end TheoremT.Polar
