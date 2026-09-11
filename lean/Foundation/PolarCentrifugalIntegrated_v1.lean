import PolarCentrifugalRay_v1
import PolarRadialKineticFubini_v1
import PolarMassCoulombMarginals_v1
import PolarInverseSquare_v1

/-! The actual ell=1 radial centrifugal bound integrated over all directions.
The inverse-square term is still present here. Its removal in the mean-zero
angular sector is a separate consequence of actual sphere Poincare. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ContDiff Topology
namespace TheoremT.Polar

theorem centrifugal_integrated_lower {f : EnergyR3 → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (h0 : (0 : EnergyR3) ∉ tsupport f)
    (Z : ℝ) :
    -(Z ^ 2 / 8) * (∫ x : EnergyR3, ‖f x‖ ^ 2) ≤
      (1 / 2) * (∫ r : ℝ in Ioi 0, r ^ 2 * (∫ w : EnergySphere,
        ‖fderiv ℝ f (r • w.val) w.val‖ ^ 2 ∂(volume : Measure EnergyR3).toSphere)) -
      Z * (∫ x : EnergyR3, ‖f x‖ ^ 2 / ‖x‖) +
      (∫ x : EnergyR3, ‖f x‖ ^ 2 / ‖x‖ ^ 2) := by
  have hm := compact_mass_sphere_marginal_integrable hf.continuous hc
  have hk := polarRadialKinetic_sphere_marginal_integrable hf hc
  have hn := compact_coulomb_sphere_marginal_integrable hf.continuous hc h0
  have hi := compact_inverseSquare_sphere_marginal_integrable hf.continuous hc h0
  have hle := integral_mono (hm.const_mul (-(Z ^ 2 / 8)))
    (((hk.const_mul (1 / 2)).sub (hn.const_mul Z)).add hi) (fun w => by
      have hw : w.val ≠ (0 : EnergyR3) := by
        have hnrm : ‖w.val‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using w.property
        intro hw
        simp [hw] at hnrm
      exact RadialProfile.centrifugal_ray_lower f hf hc h0 w.val hw Z)
  simp only [Pi.add_apply, Pi.sub_apply] at hle
  have hsub := (hk.const_mul (1 / 2)).sub (hn.const_mul Z)
  have hadd := integral_add hsub hi
  simp only [Pi.sub_apply] at hadd
  rw [integral_const_mul, hadd,
    integral_sub (hk.const_mul (1 / 2)) (hn.const_mul Z),
    integral_const_mul, integral_const_mul,
    ← compact_mass_polar_sphere_outer hf.continuous hc,
    ← compact_coulomb_polar_sphere_outer hf.continuous hc h0,
    ← compact_inverseSquare_polar_sphere_outer hf.continuous hc h0,
    polarRadialKinetic_fubini hf hc] at hle
  exact hle

end TheoremT.Polar
