import CompactRealOscillatorSquare_v1
import Mathlib.Analysis.Complex.RealDeriv

noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory
namespace TheoremT.Continuum
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

theorem compact_complex_norm_sq_integral_split {u : E → ℂ}
    (hu : Continuous u) (hc : HasCompactSupport u) :
    (∫ x, ‖u x‖^2 ∂μ)=(∫ x, (u x).re^2 ∂μ)+(∫ x, (u x).im^2 ∂μ) := by
  have hr : Integrable (fun x => (u x).re^2) μ :=
    compact_real_square_integrable_general (Complex.continuous_re.comp hu) (hc.comp_left (by rfl))
  have hi : Integrable (fun x => (u x).im^2) μ :=
    compact_real_square_integrable_general (Complex.continuous_im.comp hu) (hc.comp_left (by rfl))
  have he : (fun x => ‖u x‖^2)=(fun x => (u x).re^2+(u x).im^2) := by
    funext x
    rw [Complex.sq_norm,Complex.normSq_apply]
    ring
  rw [he,integral_add hr hi]

theorem compact_complex_oscillator_directional_bound (L : E →L[ℝ] ℝ) (v : E) (hLv : L v=1)
    {u : E → ℂ} (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u) (a : ℝ) :
    a*(∫ x, ‖u x‖^2 ∂μ) ≤
      (∫ x, ‖fderiv ℝ u x v‖^2 ∂μ)+a^2*(∫ x, ‖L x • u x‖^2 ∂μ) := by
  have hre : ContDiff ℝ 1 (fun x => (u x).re) := Complex.reCLM.contDiff.comp hu
  have him : ContDiff ℝ 1 (fun x => (u x).im) := Complex.imCLM.contDiff.comp hu
  have hcre : HasCompactSupport (fun x => (u x).re) := hc.comp_left (by rfl)
  have hcim : HasCompactSupport (fun x => (u x).im) := hc.comp_left (by rfl)
  have hr := compact_real_oscillator_directional_bound (μ := μ) L v hLv hre hcre a
  have hi := compact_real_oscillator_directional_bound (μ := μ) L v hLv him hcim a
  have hD : Continuous (fun x => fderiv ℝ u x v) :=
    (hu.continuous_fderiv_apply (by norm_num)).comp (continuous_id.prodMk continuous_const)
  have hreD (x : E) : fderiv ℝ (fun y => (u y).re) x v=(fderiv ℝ u x v).re := by
    have h := Complex.reCLM.hasFDerivAt.comp x ((hu.differentiable (by norm_num) x).hasFDerivAt)
    exact congrArg (fun A : E →L[ℝ] ℝ => A v) h.fderiv
  have himD (x : E) : fderiv ℝ (fun y => (u y).im) x v=(fderiv ℝ u x v).im := by
    have h := Complex.imCLM.hasFDerivAt.comp x ((hu.differentiable (by norm_num) x).hasFDerivAt)
    exact congrArg (fun A : E →L[ℝ] ℝ => A v) h.fderiv
  simp_rw [hreD] at hr
  simp_rw [himD] at hi
  have hWr : Integrable (fun x => (L x*(u x).re)^2) μ :=
    compact_real_square_integrable_general (L.continuous.mul hre.continuous) hcre.mul_left
  have hWi : Integrable (fun x => (L x*(u x).im)^2) μ :=
    compact_real_square_integrable_general (L.continuous.mul him.continuous) hcim.mul_left
  have hW : (fun x => ‖L x • u x‖^2)=(fun x => (L x*(u x).re)^2+(L x*(u x).im)^2) := by
    funext x
    rw [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,Complex.sq_norm,Complex.normSq_apply]
    ring
  rw [compact_complex_norm_sq_integral_split (μ := μ) hu.continuous hc,
    compact_complex_norm_sq_integral_split (μ := μ) hD (hc.fderiv_apply ℝ v),hW,
    integral_add hWr hWi]
  nlinarith only [hr,hi]

#print axioms compact_complex_norm_sq_integral_split
#print axioms compact_complex_oscillator_directional_bound
end TheoremT.Continuum
