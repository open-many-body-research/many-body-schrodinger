import NormalizedRadialMeanTest_v1
import HalfLineRadialKinetic_v2
import HalfLinePhysicalForm_v1

/-! Literal norm, kinetic and nuclear integrals of the actual normalized
spherical mean profile in the physical half-line domain. -/
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace TheoremT.Polar.MeanProfile
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
variable (f : E → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
  (hz : (0 : E) ∉ tsupport f)

def meanDomain : TheoremT.HalfLine.D :=
  TheoremT.HalfLine.testEmbed (normalizedMeanTest f hf hc hz)

theorem meanDomain_value_ae :
    TheoremT.HalfLine.J (meanDomain f hf hc hz) =ᵐ[TheoremT.HalfLine.μ]
      fun r => r • normalizedRadialMean f r := normalizedMeanTest_value_ae f hf hc hz

theorem meanDomain_quotient_ae :
    TheoremT.HalfLine.W (meanDomain f hf hc hz) =ᵐ[TheoremT.HalfLine.μ]
      fun r => normalizedRadialMean f r := by
  filter_upwards [TheoremT.HalfLine.W_coe (meanDomain f hf hc hz),
    meanDomain_value_ae f hf hc hz,ae_restrict_mem measurableSet_Ioi] with r hW hv hr
  rw [hW,hv,smul_smul,inv_mul_cancel₀ (ne_of_gt hr),one_smul]

theorem meanDomain_adjusted_derivative_ae :
    (TheoremT.HalfLine.dJ (meanDomain f hf hc hz)-
      TheoremT.HalfLine.W (meanDomain f hf hc hz)) =ᵐ[TheoremT.HalfLine.μ]
      fun r => r • (normalizedRadialDerivativeMean f r) := by
  filter_upwards [Lp.coeFn_sub (TheoremT.HalfLine.dJ (meanDomain f hf hc hz))
      (TheoremT.HalfLine.W (meanDomain f hf hc hz)),
    normalizedMeanTest_gradient_ae f hf hc hz,meanDomain_quotient_ae f hf hc hz]
      with r hs hd hW
  simp only [Pi.sub_apply] at hs
  change TheoremT.HalfLine.dJ (meanDomain f hf hc hz) r =
    normalizedRadialMean f r+r • (normalizedRadialDerivativeMean f r) at hd
  rw [hs,hd,hW]
  abel

theorem meanDomain_norm_integral :
    ‖TheoremT.HalfLine.J (meanDomain f hf hc hz)‖^2 =
      ∫ r, r^2 * ‖normalizedRadialMean f r‖^2 ∂TheoremT.HalfLine.μ := by
  rw [TheoremT.HalfLine.l2_norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [meanDomain_value_ae f hf hc hz] with r hr
  rw [hr,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]

theorem meanDomain_kinetic_integral :
    ‖TheoremT.HalfLine.dJ (meanDomain f hf hc hz)‖^2 =
      ∫ r, r^2 * ‖normalizedRadialDerivativeMean f r‖^2 ∂TheoremT.HalfLine.μ := by
  rw [← TheoremT.HalfLine.radial_kinetic_cancellation_v2,
    TheoremT.HalfLine.l2_norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [meanDomain_adjusted_derivative_ae f hf hc hz] with r hr
  rw [hr,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]

theorem meanDomain_nuclear_integral :
    TheoremT.HalfLine.coulombMoment (meanDomain f hf hc hz) =
      ∫ r, r * ‖normalizedRadialMean f r‖^2 ∂TheoremT.HalfLine.μ := by
  rw [TheoremT.HalfLine.coulombMoment_integral]
  apply integral_congr_ae
  filter_upwards [meanDomain_value_ae f hf hc hz,
    ae_restrict_mem measurableSet_Ioi] with r hv hr
  rw [hv,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
  have hn : r ≠ 0 := ne_of_gt hr
  field_simp
  <;> ring

theorem meanDomain_q_integral (Z : ℝ) :
    TheoremT.HalfLine.q Z (meanDomain f hf hc hz) =
      (1/2)*(∫ r, r^2 * ‖normalizedRadialDerivativeMean f r‖^2 ∂TheoremT.HalfLine.μ) -
      Z*(∫ r, r * ‖normalizedRadialMean f r‖^2 ∂TheoremT.HalfLine.μ) := by
  rw [TheoremT.HalfLine.q,meanDomain_kinetic_integral,meanDomain_nuclear_integral]

#print axioms meanDomain_value_ae
#print axioms meanDomain_quotient_ae
#print axioms meanDomain_adjusted_derivative_ae
#print axioms meanDomain_norm_integral
#print axioms meanDomain_kinetic_integral
#print axioms meanDomain_nuclear_integral
#print axioms meanDomain_q_integral
end TheoremT.Polar.MeanProfile
