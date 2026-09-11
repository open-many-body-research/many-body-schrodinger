import PolarGroundNormalization_v1

/-! Exact projection compatibility between the actual spatial exponential
and the actual half-line mean domain. The input L2 representative is explicit. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace TheoremT.Polar
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem area_smul_normalizedRadialMean (f : E → ℂ) (r : ℝ) :
    (4 * Real.pi) • normalizedRadialMean f r = sphereAverage f r := by
  rw [normalizedRadialMean, smul_smul, mul_inv_cancel₀ (by positivity : (4 * Real.pi) ≠ 0),
    one_smul]

theorem radialGround_inner_mean_integral (Z : ℝ) (hZ : 0 < Z)
    (f : E → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hz : (0 : E) ∉ tsupport f) :
    inner ℂ (TheoremT.HalfLine.radialGroundL2 Z hZ)
      (TheoremT.HalfLine.J (MeanProfile.meanDomain f hf hc hz)) =
    ∫ r in Ioi (0 : ℝ), r ^ 2 •
      inner ℂ (TheoremT.HalfLine.radialExp Z r) (normalizedRadialMean f r) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [TheoremT.HalfLine.radialGroundL2_coe Z hZ,
    MeanProfile.meanDomain_value_ae f hf hc hz] with r hg hu
  rw [hg, hu]
  have he : TheoremT.HalfLine.radialGround Z r = r • TheoremT.HalfLine.radialExp Z r := by
    simp only [TheoremT.HalfLine.radialGround, Complex.real_smul]
  rw [he, inner_smul_left_eq_smul, inner_smul_right_eq_smul, smul_smul, pow_two]

theorem polarGround_inner_mean (hdim : Module.finrank ℝ E = 3) (Z : ℝ) (hZ : 0 < Z)
    (f : E → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hz : (0 : E) ∉ tsupport f)
    (g : Lp ℂ 2 (volume : Measure E)) (hg : (g : E → ℂ) =ᵐ[volume] f) :
    inner ℂ (polarGroundL2 hdim Z hZ) g = (4 * Real.pi) •
      inner ℂ (TheoremT.HalfLine.radialGroundL2 Z hZ)
        (TheoremT.HalfLine.J (MeanProfile.meanDomain f hf hc hz)) := by
  have he : (fun x : E => inner ℂ (polarGroundL2 hdim Z hZ x) (g x)) =ᵐ[volume]
      (fun x => inner ℂ (polarGroundFunction Z x) (f x)) := by
    filter_upwards [polarGroundL2_coe hdim Z hZ, hg] with x h0 h1
    rw [h0, h1]
  have hi : Integrable (fun x : E => inner ℂ (polarGroundFunction Z x) (f x)) volume :=
    (L2.integrable_inner (𝕜 := ℂ) (polarGroundL2 hdim Z hZ) g).congr he
  rw [L2.inner_def, integral_congr_ae he,
    integral_polar_dim_three_radius_outer hdim _ hi,
    radialGround_inner_mean_integral Z hZ f hf hc hz, ← integral_smul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have ha : (∫ w : Metric.sphere (0 : E) 1,
      inner ℂ (polarGroundFunction Z (r • w.val)) (f (r • w.val)) ∂sphereMeasure) =
      (4 * Real.pi) • inner ℂ (TheoremT.HalfLine.radialExp Z r) (normalizedRadialMean f r) := by
    simp_rw [polarGroundFunction, norm_radius_smul_sphere, abs_of_pos (mem_Ioi.mp hr)]
    rw [integral_inner (continuous_sphere_integrable (continuous_radial_sphere_slice hf.continuous r))]
    change inner ℂ (TheoremT.HalfLine.radialExp Z r) (sphereAverage f r) = _
    rw [← area_smul_normalizedRadialMean, inner_smul_right_eq_smul]
  rw [ha, smul_smul, smul_smul, mul_comm (r ^ 2)]

#print axioms radialGround_inner_mean_integral
#print axioms polarGround_inner_mean
end TheoremT.Polar
