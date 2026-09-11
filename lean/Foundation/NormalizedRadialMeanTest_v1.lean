import SphericalVariance_v1
import PolarHalfLineTest_v1

/-! The normalized spherical mean supplies an actual smooth compact test
function on the positive half-line, including its physical derivative. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace TheoremT.Polar
open TheoremT.OneDimensional
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem normalizedRadialMean_compact {f : E → ℂ} (hc : HasCompactSupport f) :
    HasCompactSupport (normalizedRadialMean f) := by
  change HasCompactSupport (fun r : ℝ => ((4 * Real.pi)⁻¹ : ℝ) • sphereAverage f r)
  exact (sphereAverage_compact hc).smul_left (f := fun _ : ℝ => ((4 * Real.pi)⁻¹ : ℝ))

theorem normalizedRadialMean_zero_not_tsupport {f : E → ℂ}
    (hz : (0 : E) ∉ tsupport f) : (0 : ℝ) ∉ tsupport (normalizedRadialMean f) :=
  fun h => sphereAverage_zero_not_tsupport hz
    (tsupport_smul_subset_right (fun _ : ℝ => ((4 * Real.pi)⁻¹ : ℝ)) (sphereAverage f) h)

def normalizedMeanProfile (f : E → ℂ) (r : ℝ) : ℂ := r • normalizedRadialMean f r

theorem normalizedMeanProfile_contDiff {f : E → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (normalizedMeanProfile f) :=
  contDiff_id.smul (normalizedRadialMean_contDiff hf)

theorem normalizedMeanProfile_compact {f : E → ℂ} (hc : HasCompactSupport f) :
    HasCompactSupport (normalizedMeanProfile f) := by
  change HasCompactSupport (fun r : ℝ => r • normalizedRadialMean f r)
  exact (normalizedRadialMean_compact hc).smul_left (f := fun r : ℝ => r)

theorem normalizedMeanProfile_zero_not_tsupport {f : E → ℂ}
    (hz : (0 : E) ∉ tsupport f) : (0 : ℝ) ∉ tsupport (normalizedMeanProfile f) :=
  fun h => normalizedRadialMean_zero_not_tsupport hz
    (tsupport_smul_subset_right (fun r : ℝ => r) (normalizedRadialMean f) h)

theorem normalizedMeanProfile_hasDerivAt {f : E → ℂ} (hf : ContDiff ℝ ∞ f) (r : ℝ) :
    HasDerivAt (normalizedMeanProfile f)
      (normalizedRadialMean f r + r • normalizedRadialDerivativeMean f r) r := by
  simpa only [normalizedMeanProfile, one_smul, add_comm] using!
    (hasDerivAt_id' r).fun_smul (normalizedRadialMean_hasDerivAt hf r)

def normalizedMeanTest (f : E → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hz : (0 : E) ∉ tsupport f) : TheoremT.HalfLine.Test :=
  positiveRestrictionTest (normalizedMeanProfile f) (normalizedMeanProfile_contDiff hf)
    (normalizedMeanProfile_compact hc) (normalizedMeanProfile_zero_not_tsupport hz)

theorem normalizedMeanTest_value (f : E → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hz : (0 : E) ∉ tsupport f) {r : ℝ} (hr : 0 < r) :
    (normalizedMeanTest f hf hc hz : ℝ → ℂ) r = r • normalizedRadialMean f r :=
  positiveRestrictionTest_value_of_pos _ _ _ _ hr

theorem normalizedMeanTest_deriv (f : E → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hz : (0 : E) ∉ tsupport f) {r : ℝ} (hr : 0 < r) :
    deriv (normalizedMeanTest f hf hc hz : ℝ → ℂ) r =
      normalizedRadialMean f r + r • normalizedRadialDerivativeMean f r := by
  rw [normalizedMeanTest, positiveRestrictionTest_deriv_of_pos _ _ _ _ hr]
  exact (normalizedMeanProfile_hasDerivAt hf r).deriv

theorem normalizedMeanTest_value_ae (f : E → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hz : (0 : E) ∉ tsupport f) :
    (normalizedMeanTest f hf hc hz).value =ᵐ[TheoremT.HalfLine.μ]
      (fun r => r • normalizedRadialMean f r) := by
  filter_upwards [(normalizedMeanTest f hf hc hz).coe_value,
    ae_restrict_mem measurableSet_Ioi] with r hv hr
  rw [hv, normalizedMeanTest_value f hf hc hz hr]

theorem normalizedMeanTest_gradient_ae (f : E → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hz : (0 : E) ∉ tsupport f) :
    (normalizedMeanTest f hf hc hz).gradient =ᵐ[TheoremT.HalfLine.μ]
      (fun r => normalizedRadialMean f r + r • normalizedRadialDerivativeMean f r) := by
  filter_upwards [(normalizedMeanTest f hf hc hz).coe_gradient,
    ae_restrict_mem measurableSet_Ioi] with r hv hr
  rw [hv, normalizedMeanTest_deriv f hf hc hz hr]

theorem exists_actual_normalized_mean_domain (f : E → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hz : (0 : E) ∉ tsupport f) :
    ∃ u : TheoremT.HalfLine.D,
      (TheoremT.HalfLine.J u =ᵐ[TheoremT.HalfLine.μ]
        (fun r => r • normalizedRadialMean f r)) ∧
      (TheoremT.HalfLine.dJ u =ᵐ[TheoremT.HalfLine.μ]
        (fun r => normalizedRadialMean f r + r • normalizedRadialDerivativeMean f r)) := by
  exact ⟨TheoremT.HalfLine.testEmbed (normalizedMeanTest f hf hc hz),
    normalizedMeanTest_value_ae f hf hc hz, normalizedMeanTest_gradient_ae f hf hc hz⟩

#print axioms normalizedMeanTest
#print axioms normalizedMeanTest_deriv
#print axioms exists_actual_normalized_mean_domain
end TheoremT.Polar
