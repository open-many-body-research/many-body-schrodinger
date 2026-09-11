import PolarHalfLineTest_v1
import HalfLineRadialKinetic_v2
import HalfLinePhysicalForm_v1

/-! Integration v2: literal radial norm, kinetic and nuclear integrals for the actual polar
profile on the actual half-line domain. The kinetic cancellation is proved. -/
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace TheoremT.Polar.RadialProfile
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (f : E → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
  (hz : (0 : E) ∉ tsupport f) (w : E) (hw : w ≠ 0)

def radialDomain : TheoremT.HalfLine.D :=
  TheoremT.HalfLine.testEmbed (radialTest f hf hc hz w hw)

theorem radialDomain_value_ae :
    TheoremT.HalfLine.J (radialDomain f hf hc hz w hw) =ᵐ[TheoremT.HalfLine.μ]
      fun r => r • f (r • w) := radialTest_value_ae f hf hc hz w hw

theorem radialDomain_quotient_ae :
    TheoremT.HalfLine.W (radialDomain f hf hc hz w hw) =ᵐ[TheoremT.HalfLine.μ]
      fun r => f (r • w) := by
  filter_upwards [TheoremT.HalfLine.W_coe (radialDomain f hf hc hz w hw),
    radialDomain_value_ae f hf hc hz w hw,ae_restrict_mem measurableSet_Ioi] with r hW hv hr
  rw [hW,hv,smul_smul,inv_mul_cancel₀ (ne_of_gt hr),one_smul]

theorem radialDomain_adjusted_derivative_ae :
    (TheoremT.HalfLine.dJ (radialDomain f hf hc hz w hw)-
      TheoremT.HalfLine.W (radialDomain f hf hc hz w hw)) =ᵐ[TheoremT.HalfLine.μ]
      fun r => r • (fderiv ℝ f (r • w) w) := by
  filter_upwards [Lp.coeFn_sub (TheoremT.HalfLine.dJ (radialDomain f hf hc hz w hw))
      (TheoremT.HalfLine.W (radialDomain f hf hc hz w hw)),
    radialTest_gradient_ae f hf hc hz w hw,radialDomain_quotient_ae f hf hc hz w hw]
      with r hs hd hW
  simp only [Pi.sub_apply] at hs
  change TheoremT.HalfLine.dJ (radialDomain f hf hc hz w hw) r =
    f (r • w)+r • (fderiv ℝ f (r • w) w) at hd
  rw [hs,hd,hW]
  abel

theorem radialDomain_norm_integral :
    ‖TheoremT.HalfLine.J (radialDomain f hf hc hz w hw)‖^2 =
      ∫ r, r^2 * ‖f (r • w)‖^2 ∂TheoremT.HalfLine.μ := by
  rw [TheoremT.HalfLine.l2_norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [radialDomain_value_ae f hf hc hz w hw] with r hr
  rw [hr,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]

theorem radialDomain_kinetic_integral :
    ‖TheoremT.HalfLine.dJ (radialDomain f hf hc hz w hw)‖^2 =
      ∫ r, r^2 * ‖fderiv ℝ f (r • w) w‖^2 ∂TheoremT.HalfLine.μ := by
  rw [← TheoremT.HalfLine.radial_kinetic_cancellation_v2,
    TheoremT.HalfLine.l2_norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [radialDomain_adjusted_derivative_ae f hf hc hz w hw] with r hr
  rw [hr,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]

theorem radialDomain_nuclear_integral :
    TheoremT.HalfLine.coulombMoment (radialDomain f hf hc hz w hw) =
      ∫ r, r * ‖f (r • w)‖^2 ∂TheoremT.HalfLine.μ := by
  rw [TheoremT.HalfLine.coulombMoment_integral]
  apply integral_congr_ae
  filter_upwards [radialDomain_value_ae f hf hc hz w hw,
    ae_restrict_mem measurableSet_Ioi] with r hv hr
  rw [hv,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
  have hn : r ≠ 0 := ne_of_gt hr
  field_simp
  <;> ring

theorem radialDomain_q_integral (Z : ℝ) :
    TheoremT.HalfLine.q Z (radialDomain f hf hc hz w hw) =
      (1/2)*(∫ r, r^2 * ‖fderiv ℝ f (r • w) w‖^2 ∂TheoremT.HalfLine.μ) -
      Z*(∫ r, r * ‖f (r • w)‖^2 ∂TheoremT.HalfLine.μ) := by
  rw [TheoremT.HalfLine.q,radialDomain_kinetic_integral,radialDomain_nuclear_integral]

#print axioms radialDomain_value_ae
#print axioms radialDomain_quotient_ae
#print axioms radialDomain_adjusted_derivative_ae
#print axioms radialDomain_norm_integral
#print axioms radialDomain_kinetic_integral
#print axioms radialDomain_nuclear_integral
#print axioms radialDomain_q_integral
end TheoremT.Polar.RadialProfile
