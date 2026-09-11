import PhysicalRadialMean_v1

/-! Radial differentiation of the actual physical mean and fluctuation.
All identities involve actual Fréchet derivatives at positive radii. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace TheoremT.Polar
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem physicalRadialMean_ray_hasDerivAt {f : E → ℂ} (hf : ContDiff ℝ ∞ f)
    (w : Metric.sphere (0 : E) 1) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s : ℝ => physicalRadialMean f (s • w.val))
      (normalizedRadialDerivativeMean f r) r := by
  apply (normalizedRadialMean_hasDerivAt hf r).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds hr] with s hs
  exact physicalRadialMean_on_ray f w (le_of_lt hs)

theorem physicalRadialMean_radial_fderiv {f : E → ℂ} (hf : ContDiff ℝ ∞ f)
    (hz : (0 : E) ∉ tsupport f) (w : Metric.sphere (0 : E) 1)
    {r : ℝ} (hr : 0 < r) :
    fderiv ℝ (physicalRadialMean f) (r • w.val) w.val = normalizedRadialDerivativeMean f r := by
  have hactual : HasDerivAt (fun s : ℝ => physicalRadialMean f (s • w.val))
      (fderiv ℝ (physicalRadialMean f) (r • w.val) w.val) r := by
    simpa only [Function.comp_def, one_smul] using
      ((physicalRadialMean_contDiff hf hz).differentiable (by simp) (r • w.val)).hasFDerivAt.comp_hasDerivAt r
        ((hasDerivAt_id' r).smul_const w.val)
  exact hactual.unique (physicalRadialMean_ray_hasDerivAt hf w hr)

theorem physicalFluctuation_radial_fderiv {f : E → ℂ} (hf : ContDiff ℝ ∞ f)
    (hz : (0 : E) ∉ tsupport f) (w : Metric.sphere (0 : E) 1)
    {r : ℝ} (hr : 0 < r) :
    fderiv ℝ (physicalFluctuation f) (r • w.val) w.val =
      fderiv ℝ f (r • w.val) w.val - normalizedRadialDerivativeMean f r := by
  change fderiv ℝ (f - physicalRadialMean f) (r • w.val) w.val = _
  rw [fderiv_sub (hf.differentiable (by simp) (r • w.val))
    ((physicalRadialMean_contDiff hf hz).differentiable (by simp) (r • w.val)),
    ContinuousLinearMap.sub_apply, physicalRadialMean_radial_fderiv hf hz w hr]

theorem physicalFluctuation_radial_fderiv_mean_zero
    (hdim : Module.finrank ℝ E = 3) {f : E → ℂ} (hf : ContDiff ℝ ∞ f)
    (hz : (0 : E) ∉ tsupport f) {r : ℝ} (hr : 0 < r) :
    (∫ w : Metric.sphere (0 : E) 1,
      fderiv ℝ (physicalFluctuation f) (r • w.val) w.val ∂sphereMeasure) = 0 := by
  simp_rw [physicalFluctuation_radial_fderiv hf hz _ hr]
  exact radial_derivative_fluctuation_mean_zero hdim hf r

#print axioms physicalRadialMean_radial_fderiv
#print axioms physicalFluctuation_radial_fderiv
#print axioms physicalFluctuation_radial_fderiv_mean_zero
end TheoremT.Polar
