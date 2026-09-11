import NormalizedMeanIntegrals_v1

/-! Actual half-line mean mass, nuclear and kinetic integrability, derived
from the established D membership and its L2 representatives. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff
namespace TheoremT.Polar.MeanProfile
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
variable (f : E → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
  (hz : (0 : E) ∉ tsupport f)
include hf hc hz

theorem mean_mass_integrable :
    IntegrableOn (fun r : ℝ => r^2 * ‖normalizedRadialMean f r‖^2) (Ioi 0) := by
  have hi : Integrable (fun r => ‖TheoremT.HalfLine.J (meanDomain f hf hc hz) r‖^2)
      TheoremT.HalfLine.μ := by
    simpa only [real_inner_self_eq_norm_sq] using L2.integrable_inner (𝕜 := ℝ)
      (TheoremT.HalfLine.J (meanDomain f hf hc hz))
      (TheoremT.HalfLine.J (meanDomain f hf hc hz))
  apply hi.congr
  filter_upwards [meanDomain_value_ae f hf hc hz] with r hr
  rw [hr,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]

theorem mean_nuclear_integrable :
    IntegrableOn (fun r : ℝ => r * ‖normalizedRadialMean f r‖^2) (Ioi 0) := by
  apply (TheoremT.HalfLine.coulombMoment_integrable (meanDomain f hf hc hz)).congr
  filter_upwards [meanDomain_value_ae f hf hc hz,
    ae_restrict_mem measurableSet_Ioi] with r hr hp
  rw [hr,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
  have hn : r ≠ 0 := ne_of_gt hp
  field_simp
  <;> ring

theorem mean_radial_kinetic_integrable :
    IntegrableOn (fun r : ℝ => r^2 * ‖normalizedRadialDerivativeMean f r‖^2) (Ioi 0) := by
  let v := TheoremT.HalfLine.dJ (meanDomain f hf hc hz) -
    TheoremT.HalfLine.W (meanDomain f hf hc hz)
  have hi : Integrable (fun r => ‖v r‖^2) TheoremT.HalfLine.μ := by
    simpa only [real_inner_self_eq_norm_sq] using L2.integrable_inner (𝕜 := ℝ) v v
  apply hi.congr
  filter_upwards [meanDomain_adjusted_derivative_ae f hf hc hz] with r hr
  change v r = r • normalizedRadialDerivativeMean f r at hr
  rw [hr,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]

#print axioms mean_mass_integrable
#print axioms mean_nuclear_integrable
#print axioms mean_radial_kinetic_integrable
end TheoremT.Polar.MeanProfile
