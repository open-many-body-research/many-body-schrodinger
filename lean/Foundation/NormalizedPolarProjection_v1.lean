import PolarGroundProjection_v1

/-! Exact squared projection onto the normalized spatial exponential equals
sphere area times the squared normalized half-line mean projection. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace TheoremT.Polar

theorem norm_inner_normalized_sq {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] (u v : F) :
    ‖inner ℂ ((‖u‖⁻¹ : ℂ) • u) v‖ ^ 2 = ‖inner ℂ u v‖ ^ 2 / ‖u‖ ^ 2 := by
  rw [inner_smul_left, norm_mul, mul_pow]
  simp only [map_inv₀, Complex.conj_ofReal, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_norm, inv_pow]
  ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem normalizedPolarGround_projection_sq (hdim : Module.finrank ℝ E = 3)
    (Z : ℝ) (hZ : 0 < Z) (f : E → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hz : (0 : E) ∉ tsupport f)
    (g : Lp ℂ 2 (volume : Measure E)) (hg : (g : E → ℂ) =ᵐ[volume] f) :
    ‖inner ℂ (normalizedPolarGround hdim Z hZ) g‖ ^ 2 =
      (4 * Real.pi) * ‖inner ℂ (TheoremT.HalfLine.normalizedGround Z hZ)
        (TheoremT.HalfLine.J (MeanProfile.meanDomain f hf hc hz))‖ ^ 2 := by
  rw [normalizedPolarGround, norm_inner_normalized_sq,
    TheoremT.HalfLine.normalizedGround_eq, norm_inner_normalized_sq,
    polarGround_inner_mean hdim Z hZ f hf hc hz g hg, norm_smul, mul_pow,
    Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 4 * Real.pi),
    polarGroundL2_norm_sq hdim Z hZ]
  have harea : (4 * Real.pi) ≠ 0 := by positivity
  have hn : ‖TheoremT.HalfLine.radialGroundL2 Z hZ‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (TheoremT.HalfLine.radialGroundL2_ne_zero Z hZ)
  field_simp
  <;> ring

#print axioms norm_inner_normalized_sq
#print axioms normalizedPolarGround_projection_sq
end TheoremT.Polar
