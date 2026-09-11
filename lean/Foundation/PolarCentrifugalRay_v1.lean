import PolarRadialIntegrals_v2
import HalfLineCentrifugal_v1

/-! The actual radial transform r f(rw) satisfies the ell=1 centrifugal
comparison on every nonzero direction. No angular decomposition is assumed;
all terms below are literal ray integrals of the physical function. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace TheoremT.Polar.RadialProfile
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (f : E → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
  (hz : (0 : E) ∉ tsupport f) (w : E) (hw : w ≠ 0)

theorem radialDomain_quotient_norm_integral :
    ‖TheoremT.HalfLine.W (radialDomain f hf hc hz w hw)‖ ^ 2 =
      ∫ r, ‖f (r • w)‖ ^ 2 ∂TheoremT.HalfLine.μ := by
  rw [TheoremT.HalfLine.l2_norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [radialDomain_quotient_ae f hf hc hz w hw] with r hr
  rw [hr]

include hf hc hz hw in
theorem centrifugal_ray_lower (Z : ℝ) :
    -(Z ^ 2 / 8) * (∫ r : ℝ in Ioi 0, r ^ 2 * ‖f (r • w)‖ ^ 2) ≤
      (1 / 2) * (∫ r : ℝ in Ioi 0, r ^ 2 * ‖fderiv ℝ f (r • w) w‖ ^ 2) -
        Z * (∫ r : ℝ in Ioi 0, r * ‖f (r • w)‖ ^ 2) +
        (∫ r : ℝ in Ioi 0, ‖f (r • w)‖ ^ 2) := by
  have h := TheoremT.HalfLine.centrifugal_one_lower Z (radialDomain f hf hc hz w hw)
  rw [radialDomain_norm_integral f hf hc hz w hw,
    radialDomain_q_integral f hf hc hz w hw Z,
    radialDomain_quotient_norm_integral f hf hc hz w hw] at h
  exact h

end TheoremT.Polar.RadialProfile
