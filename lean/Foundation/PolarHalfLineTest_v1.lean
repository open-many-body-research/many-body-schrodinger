import PolarRadialProfile_v1
import PositiveHalfLineRestriction_v1
import HalfLineCoreDensity_v1

/-! The physical radial transform r f(rw) of every punctured smooth compact
input belongs to the actual half-line test domain. Its value and derivative
are identified almost everywhere on the positive ray. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace TheoremT.Polar
open TheoremT.OneDimensional
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def radialTest (f : E → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hz : (0 : E) ∉ tsupport f) (w : E) (hw : w ≠ 0) : TheoremT.HalfLine.Test :=
  positiveRestrictionTest (radialWhole f w) (radialWhole_contDiff f hf w)
    (radialWhole_compact f hc w hw) (radialWhole_zero_notMem_tsupport f hz w)

theorem radialTest_value (f : E → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hz : (0 : E) ∉ tsupport f) (w : E) (hw : w ≠ 0) {r : ℝ} (hr : 0 < r) :
    (radialTest f hf hc hz w hw : ℝ → ℂ) r = r • f (r • w) :=
  positiveRestrictionTest_value_of_pos _ _ _ _ hr

theorem radialTest_deriv (f : E → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hz : (0 : E) ∉ tsupport f) (w : E) (hw : w ≠ 0) {r : ℝ} (hr : 0 < r) :
    deriv (radialTest f hf hc hz w hw : ℝ → ℂ) r =
      f (r • w)+r • (fderiv ℝ f (r • w) w) := by
  rw [radialTest,positiveRestrictionTest_deriv_of_pos _ _ _ _ hr]
  exact (radialWhole_hasDerivAt f hf w r).deriv

theorem radialTest_value_ae (f : E → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hz : (0 : E) ∉ tsupport f) (w : E) (hw : w ≠ 0) :
    (radialTest f hf hc hz w hw).value =ᵐ[TheoremT.HalfLine.μ]
      (fun r => r • f (r • w)) := by
  filter_upwards [(radialTest f hf hc hz w hw).coe_value,
    ae_restrict_mem measurableSet_Ioi] with r hv hr
  rw [hv,radialTest_value f hf hc hz w hw hr]

theorem radialTest_gradient_ae (f : E → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hz : (0 : E) ∉ tsupport f) (w : E) (hw : w ≠ 0) :
    (radialTest f hf hc hz w hw).gradient =ᵐ[TheoremT.HalfLine.μ]
      (fun r => f (r • w)+r • (fderiv ℝ f (r • w) w)) := by
  filter_upwards [(radialTest f hf hc hz w hw).coe_gradient,
    ae_restrict_mem measurableSet_Ioi] with r hv hr
  rw [hv,radialTest_deriv f hf hc hz w hw hr]

theorem exists_actual_radial_domain (f : E → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hz : (0 : E) ∉ tsupport f) (w : E) (hw : w ≠ 0) :
    ∃ u : TheoremT.HalfLine.D,
      (TheoremT.HalfLine.J u =ᵐ[TheoremT.HalfLine.μ] (fun r => r • f (r • w))) ∧
      (TheoremT.HalfLine.dJ u =ᵐ[TheoremT.HalfLine.μ]
        (fun r => f (r • w)+r • (fderiv ℝ f (r • w) w))) := by
  refine ⟨TheoremT.HalfLine.testEmbed (radialTest f hf hc hz w hw),?_,?_⟩
  · exact radialTest_value_ae f hf hc hz w hw
  · exact radialTest_gradient_ae f hf hc hz w hw

#print axioms radialTest
#print axioms radialTest_value
#print axioms radialTest_deriv
#print axioms radialTest_value_ae
#print axioms radialTest_gradient_ae
#print axioms exists_actual_radial_domain
end TheoremT.Polar
