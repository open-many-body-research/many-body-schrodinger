import NormalizedMeanIntegrals_v1
import HalfLineGroundFactor_v1

/-! The actual exp(-Z|x|) vector in canonical three-dimensional volume,
normalized in L2 and quantitatively linked to the actual half-line ground. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace TheoremT.Polar
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

def polarGroundFunction (Z : ℝ) (x : E) : ℂ := TheoremT.HalfLine.radialExp Z ‖x‖

theorem polarGroundFunction_continuous (Z : ℝ) : Continuous (polarGroundFunction (E := E) Z) :=
  (TheoremT.HalfLine.radialExp_contDiff Z).continuous.comp continuous_norm

theorem polarGroundFunction_memLp (hdim : Module.finrank ℝ E = 3)
    (Z : ℝ) (hZ : 0 < Z) : MemLp (polarGroundFunction (E := E) Z) 2 volume := by
  letI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  apply (memLp_two_iff_integrable_sq_norm (polarGroundFunction_continuous Z).aestronglyMeasurable).mpr
  apply (integrable_fun_norm_addHaar (volume : Measure E)
    (f := fun r : ℝ => ‖TheoremT.HalfLine.radialExp Z r‖ ^ 2)).mpr
  have hi := (memLp_two_iff_integrable_sq_norm
    (TheoremT.HalfLine.radialGround_memLp hZ).aestronglyMeasurable).mp
      (TheoremT.HalfLine.radialGround_memLp hZ)
  simpa only [IntegrableOn, TheoremT.HalfLine.μ, hdim, Nat.reduceSub, smul_eq_mul,
    TheoremT.HalfLine.radialGround, norm_mul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, sq_abs] using hi

def polarGroundL2 (hdim : Module.finrank ℝ E = 3) (Z : ℝ) (hZ : 0 < Z) :
    Lp ℂ 2 (volume : Measure E) := (polarGroundFunction_memLp hdim Z hZ).toLp (polarGroundFunction Z)

theorem polarGroundL2_coe (hdim : Module.finrank ℝ E = 3) (Z : ℝ) (hZ : 0 < Z) :
    (polarGroundL2 hdim Z hZ : E → ℂ) =ᵐ[volume] polarGroundFunction Z :=
  (polarGroundFunction_memLp hdim Z hZ).coeFn_toLp

theorem polarGroundL2_norm_sq (hdim : Module.finrank ℝ E = 3) (Z : ℝ) (hZ : 0 < Z) :
    ‖polarGroundL2 hdim Z hZ‖ ^ 2 =
      (4 * Real.pi) * ‖TheoremT.HalfLine.radialGroundL2 Z hZ‖ ^ 2 := by
  letI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  have hfull : ‖polarGroundL2 hdim Z hZ‖ ^ 2 =
      ∫ x : E, ‖TheoremT.HalfLine.radialExp Z ‖x‖‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp_rw [real_inner_self_eq_norm_sq]
    apply integral_congr_ae
    filter_upwards [polarGroundL2_coe hdim Z hZ] with x hx
    rw [hx]
    rfl
  have hhalf : ‖TheoremT.HalfLine.radialGroundL2 Z hZ‖ ^ 2 =
      ∫ r in Ioi (0 : ℝ), r ^ 2 * ‖TheoremT.HalfLine.radialExp Z r‖ ^ 2 := by
    rw [TheoremT.HalfLine.l2_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [TheoremT.HalfLine.radialGroundL2_coe Z hZ] with r hr
    rw [hr]
    simp only [TheoremT.HalfLine.radialGround, norm_mul, mul_pow,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hfull, hhalf, integral_fun_norm_addHaar (volume : Measure E)
    (fun r : ℝ => ‖TheoremT.HalfLine.radialExp Z r‖ ^ 2),
    hdim, unit_ball_volume_real_dim_three hdim]
  norm_num only [Nat.reduceSub, smul_eq_mul, Nat.cast_ofNat]
  ring

theorem polarGroundL2_ne_zero (hdim : Module.finrank ℝ E = 3) (Z : ℝ) (hZ : 0 < Z) :
    polarGroundL2 hdim Z hZ ≠ 0 := by
  intro hz
  have hn := polarGroundL2_norm_sq hdim Z hZ
  rw [hz, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hn
  have hp : 0 < (4 * Real.pi) * ‖TheoremT.HalfLine.radialGroundL2 Z hZ‖ ^ 2 := by
    exact mul_pos (by positivity) (sq_pos_of_pos (norm_pos_iff.mpr
      (TheoremT.HalfLine.radialGroundL2_ne_zero Z hZ)))
  linarith

def normalizedPolarGround (hdim : Module.finrank ℝ E = 3) (Z : ℝ) (hZ : 0 < Z) :
    Lp ℂ 2 (volume : Measure E) :=
  (‖polarGroundL2 hdim Z hZ‖⁻¹ : ℂ) • polarGroundL2 hdim Z hZ

theorem normalizedPolarGround_norm (hdim : Module.finrank ℝ E = 3) (Z : ℝ) (hZ : 0 < Z) :
    ‖normalizedPolarGround hdim Z hZ‖ = 1 := by
  rw [normalizedPolarGround, norm_smul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀]
  exact norm_ne_zero_iff.mpr (polarGroundL2_ne_zero hdim Z hZ)

#print axioms polarGroundFunction_memLp
#print axioms polarGroundL2_norm_sq
#print axioms normalizedPolarGround_norm
end TheoremT.Polar
