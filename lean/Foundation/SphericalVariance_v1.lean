import FiniteMeasureVariance_v1
import PolarThree_v1

/-! Exact mean and fluctuation splitting for the actual three-dimensional
sphere area measure, and for physical radial slices. All integrability is
obtained from continuity on the compact sphere. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace TheoremT.Polar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

/-- Mean with respect to actual sphere area divided by its three-dimensional mass. -/
def normalizedSphereMean (h : Metric.sphere (0 : E) 1 → ℂ) : ℂ :=
  (4 * Real.pi)⁻¹ • ∫ w, h w ∂sphereMeasure

theorem normalizedSphereMean_eq_finiteMeasureMean
    (hdim : Module.finrank ℝ E = 3) (h : Metric.sphere (0 : E) 1 → ℂ) :
    normalizedSphereMean h = finiteMeasureMean sphereMeasure h := by
  simp only [normalizedSphereMean, finiteMeasureMean, sphereMeasure,
    sphere_volume_real_dim_three hdim]

theorem continuous_sphere_memLp_two {h : Metric.sphere (0 : E) 1 → ℂ}
    (hh : Continuous h) : MemLp h 2 sphereMeasure :=
  hh.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace h)

theorem continuous_sphere_integrable {h : Metric.sphere (0 : E) 1 → ℂ}
    (hh : Continuous h) : Integrable h sphereMeasure :=
  hh.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace h)

theorem normalizedSphereMean_centered_integral (hdim : Module.finrank ℝ E = 3)
    {h : Metric.sphere (0 : E) 1 → ℂ} (hh : Continuous h) :
    (∫ w, h w - normalizedSphereMean h ∂sphereMeasure) = 0 := by
  rw [normalizedSphereMean_eq_finiteMeasureMean hdim]
  apply finiteMeasureMean_centered_integral sphereMeasure
  · rw [sphereMeasure, sphere_volume_real_dim_three hdim]
    positivity
  · exact continuous_sphere_integrable hh

theorem normalizedSphereMean_centered_memLp
    {h : Metric.sphere (0 : E) 1 → ℂ} (hh : Continuous h) :
    MemLp (fun w => h w - normalizedSphereMean h) 2 sphereMeasure :=
  (continuous_sphere_memLp_two hh).sub (memLp_const _)

theorem normalizedSphereMean_variance (hdim : Module.finrank ℝ E = 3)
    {h : Metric.sphere (0 : E) 1 → ℂ} (hh : Continuous h) :
    (∫ w, ‖h w - normalizedSphereMean h‖ ^ 2 ∂sphereMeasure) +
      (4 * Real.pi) * ‖normalizedSphereMean h‖ ^ 2 =
        ∫ w, ‖h w‖ ^ 2 ∂sphereMeasure := by
  rw [normalizedSphereMean_eq_finiteMeasureMean hdim,
    ← sphere_volume_real_dim_three hdim]
  apply finiteMeasureMean_variance sphereMeasure
  · rw [sphereMeasure, sphere_volume_real_dim_three hdim]
    positivity
  · exact continuous_sphere_memLp_two hh

def normalizedRadialMean (f : E → ℂ) (r : ℝ) : ℂ :=
  (4 * Real.pi)⁻¹ • sphereAverage f r

def normalizedRadialDerivativeMean (f : E → ℂ) (r : ℝ) : ℂ :=
  normalizedSphereMean (fun w : Metric.sphere (0 : E) 1 => fderiv ℝ f (r • w.val) w.val)

theorem normalizedRadialMean_eq_sphereMean (f : E → ℂ) (r : ℝ) :
    normalizedRadialMean f r =
      normalizedSphereMean (fun w : Metric.sphere (0 : E) 1 => f (r • w.val)) := rfl

theorem continuous_radial_sphere_slice {f : E → ℂ} (hf : Continuous f) (r : ℝ) :
    Continuous (fun w : Metric.sphere (0 : E) 1 => f (r • w.val)) :=
  hf.comp (continuous_const.smul continuous_subtype_val)

theorem continuous_radial_derivative_sphere_slice {f : E → ℂ}
    (hf : ContDiff ℝ ∞ f) (r : ℝ) :
    Continuous (fun w : Metric.sphere (0 : E) 1 => fderiv ℝ f (r • w.val) w.val) :=
  ((hf.continuous_fderiv (by simp)).comp
    (continuous_const.smul continuous_subtype_val)).clm_apply continuous_subtype_val

theorem normalizedRadialMean_hasDerivAt {f : E → ℂ}
    (hf : ContDiff ℝ ∞ f) (r : ℝ) :
    HasDerivAt (normalizedRadialMean f) (normalizedRadialDerivativeMean f r) r := by
  exact (sphereAverage_hasDerivAt hf r).const_smul ((4 * Real.pi)⁻¹ : ℝ)

theorem normalizedRadialMean_deriv {f : E → ℂ}
    (hf : ContDiff ℝ ∞ f) (r : ℝ) :
    deriv (normalizedRadialMean f) r = normalizedRadialDerivativeMean f r :=
  (normalizedRadialMean_hasDerivAt hf r).deriv

theorem normalizedRadialMean_contDiff {f : E → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (normalizedRadialMean f) := by
  change ContDiff ℝ ∞ (fun r : ℝ => ((4 * Real.pi)⁻¹ : ℝ) • sphereAverage f r)
  exact (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => ((4 * Real.pi)⁻¹ : ℝ))).smul
    (sphereAverage_contDiff hf)

theorem radial_fluctuation_mean_zero (hdim : Module.finrank ℝ E = 3)
    {f : E → ℂ} (hf : Continuous f) (r : ℝ) :
    (∫ w : Metric.sphere (0 : E) 1,
      f (r • w.val) - normalizedRadialMean f r ∂sphereMeasure) = 0 :=
  normalizedSphereMean_centered_integral hdim (continuous_radial_sphere_slice hf r)

theorem radial_fluctuation_variance (hdim : Module.finrank ℝ E = 3)
    {f : E → ℂ} (hf : Continuous f) (r : ℝ) :
    (∫ w : Metric.sphere (0 : E) 1,
      ‖f (r • w.val) - normalizedRadialMean f r‖ ^ 2 ∂sphereMeasure) +
      (4 * Real.pi) * ‖normalizedRadialMean f r‖ ^ 2 =
      ∫ w : Metric.sphere (0 : E) 1, ‖f (r • w.val)‖ ^ 2 ∂sphereMeasure :=
  normalizedSphereMean_variance hdim (continuous_radial_sphere_slice hf r)

theorem radial_derivative_fluctuation_mean_zero (hdim : Module.finrank ℝ E = 3)
    {f : E → ℂ} (hf : ContDiff ℝ ∞ f) (r : ℝ) :
    (∫ w : Metric.sphere (0 : E) 1,
      fderiv ℝ f (r • w.val) w.val - normalizedRadialDerivativeMean f r ∂sphereMeasure) = 0 :=
  normalizedSphereMean_centered_integral hdim (continuous_radial_derivative_sphere_slice hf r)

theorem radial_derivative_fluctuation_variance (hdim : Module.finrank ℝ E = 3)
    {f : E → ℂ} (hf : ContDiff ℝ ∞ f) (r : ℝ) :
    (∫ w : Metric.sphere (0 : E) 1,
      ‖fderiv ℝ f (r • w.val) w.val - normalizedRadialDerivativeMean f r‖ ^ 2 ∂sphereMeasure) +
      (4 * Real.pi) * ‖normalizedRadialDerivativeMean f r‖ ^ 2 =
      ∫ w : Metric.sphere (0 : E) 1, ‖fderiv ℝ f (r • w.val) w.val‖ ^ 2 ∂sphereMeasure :=
  normalizedSphereMean_variance hdim (continuous_radial_derivative_sphere_slice hf r)

theorem radial_fluctuation_memLp {f : E → ℂ} (hf : Continuous f) (r : ℝ) :
    MemLp (fun w : Metric.sphere (0 : E) 1 =>
      f (r • w.val) - normalizedRadialMean f r) 2 sphereMeasure :=
  normalizedSphereMean_centered_memLp (continuous_radial_sphere_slice hf r)

theorem radial_fluctuation_sq_integrable {f : E → ℂ} (hf : Continuous f) (r : ℝ) :
    Integrable (fun w : Metric.sphere (0 : E) 1 =>
      ‖f (r • w.val) - normalizedRadialMean f r‖ ^ 2) sphereMeasure :=
  (memLp_two_iff_integrable_sq_norm
    (radial_fluctuation_memLp hf r).aestronglyMeasurable).mp (radial_fluctuation_memLp hf r)

theorem radial_derivative_fluctuation_memLp {f : E → ℂ}
    (hf : ContDiff ℝ ∞ f) (r : ℝ) :
    MemLp (fun w : Metric.sphere (0 : E) 1 =>
      fderiv ℝ f (r • w.val) w.val - normalizedRadialDerivativeMean f r) 2 sphereMeasure :=
  normalizedSphereMean_centered_memLp (continuous_radial_derivative_sphere_slice hf r)

theorem radial_derivative_fluctuation_sq_integrable {f : E → ℂ}
    (hf : ContDiff ℝ ∞ f) (r : ℝ) :
    Integrable (fun w : Metric.sphere (0 : E) 1 =>
      ‖fderiv ℝ f (r • w.val) w.val - normalizedRadialDerivativeMean f r‖ ^ 2) sphereMeasure :=
  (memLp_two_iff_integrable_sq_norm
    (radial_derivative_fluctuation_memLp hf r).aestronglyMeasurable).mp
      (radial_derivative_fluctuation_memLp hf r)

#print axioms normalizedSphereMean_centered_integral
#print axioms normalizedSphereMean_variance
#print axioms normalizedRadialMean_hasDerivAt
#print axioms radial_fluctuation_variance
#print axioms radial_derivative_fluctuation_variance
end TheoremT.Polar
