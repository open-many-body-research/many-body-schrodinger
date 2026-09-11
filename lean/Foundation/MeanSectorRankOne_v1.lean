import NormalizedPolarProjection_v1
import HalfLineHydrogenRankOne_v1

/-! Actual normalized spherical-mean sector comparison with the physical
three-dimensional normalized exponential projection. No spectral separation
or half-line membership is supplied as an extra assumption. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace TheoremT.Polar
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem physical_mean_sector_rank_one (hdim : Module.finrank ℝ E = 3)
    (Z : ℝ) (hZ : 0 < Z) (f : E → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hz : (0 : E) ∉ tsupport f)
    (g : Lp ℂ 2 (volume : Measure E)) (hg : (g : E → ℂ) =ᵐ[volume] f) :
    -(Z ^ 2 / 8) * ((4 * Real.pi) *
      (∫ r in Ioi (0 : ℝ), r ^ 2 * ‖normalizedRadialMean f r‖ ^ 2)) -
      (3 * Z ^ 2 / 8) * ‖inner ℂ (normalizedPolarGround hdim Z hZ) g‖ ^ 2 ≤
      (4 * Real.pi) * ((1 / 2) *
        (∫ r in Ioi (0 : ℝ), r ^ 2 * ‖normalizedRadialDerivativeMean f r‖ ^ 2) -
        Z * (∫ r in Ioi (0 : ℝ), r * ‖normalizedRadialMean f r‖ ^ 2)) := by
  have h := mul_le_mul_of_nonneg_left
    (TheoremT.HalfLine.hydrogen_radial_rank_one Z hZ (MeanProfile.meanDomain f hf hc hz))
    (by positivity : 0 ≤ 4 * Real.pi)
  rw [MeanProfile.meanDomain_norm_integral, MeanProfile.meanDomain_q_integral] at h
  rw [normalizedPolarGround_projection_sq hdim Z hZ f hf hc hz g hg]
  simpa only [TheoremT.HalfLine.μ, mul_sub, mul_assoc, mul_left_comm, mul_comm] using h

#print axioms physical_mean_sector_rank_one
end TheoremT.Polar
