import YoungConvolutionExists_v1
import ActualL2IntegralCauchy_v1

noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped ENNReal
namespace TheoremT.Continuum
variable {T F : Type*} [MeasurableSpace T] [AddCommGroup T]
  [MeasurableAdd₂ T] [MeasurableNeg T] {ν : Measure T} [SFinite ν]
  [IsAddRightInvariant ν] [IsAddLeftInvariant ν] [IsNegInvariant ν]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem real_kernel_convolution_l2_memLp {K : T → ℝ} {f : T → F}
    (hK : StronglyMeasurable K) (hKi : Integrable K ν)
    (hf : StronglyMeasurable f) (hf2 : MemLp f 2 ν) :
    MemLp (fun t => ∫ s, K s • f (t-s) ∂ν) 2 ν := by
  simpa only [ENNReal.ofReal_one,ENNReal.ofReal_ofNat] using
    young_bochner_smul_memLp hK hf
      (p := 1) (q := 2) (r := 2) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by simpa using memLp_one_iff_integrable.mpr hKi) (by simpa using hf2)

theorem real_kernel_convolution_l2_norm_le {K : T → ℝ} {f : T → F}
    (hK : StronglyMeasurable K) (hKi : Integrable K ν)
    (hf : StronglyMeasurable f) (hf2 : MemLp f 2 ν) :
    ‖(real_kernel_convolution_l2_memLp hK hKi hf hf2).toLp
      (fun t => ∫ s, K s • f (t-s) ∂ν)‖ ≤
      (∫ s,‖K s‖ ∂ν)*‖hf2.toLp f‖ := by
  have hb : eLpNorm (fun t => ∫ s, K s • f (t-s) ∂ν) 2 ν ≤
      eLpNorm K 1 ν*eLpNorm f 2 ν := by
    simpa only [ENNReal.ofReal_one,ENNReal.ofReal_ofNat] using
      young_bochner_smul_eLpNorm_le hK hf
        (p := 1) (q := 2) (r := 2) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num)
  rw [Lp.norm_toLp,Lp.norm_toLp,integral_norm_eq_lintegral_enorm hK.aestronglyMeasurable,
    ← eLpNorm_one_eq_lintegral_enorm,← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono
    (ENNReal.mul_ne_top (memLp_one_iff_integrable.mpr hKi).eLpNorm_ne_top hf2.eLpNorm_ne_top) hb

theorem real_kernel_convolution_l2_integral_le {K : T → ℝ} {f : T → F}
    (hK : StronglyMeasurable K) (hKi : Integrable K ν)
    (hf : StronglyMeasurable f) (hf2 : MemLp f 2 ν) :
    (∫ t,‖∫ s,K s • f (t-s) ∂ν‖^2 ∂ν) ≤
      (∫ s,‖K s‖ ∂ν)^2*(∫ t,‖f t‖^2 ∂ν) := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (real_kernel_convolution_l2_norm_le hK hKi hf hf2) 2
  simpa only [mul_pow,actual_l2_toLp_norm_sq_integral] using h

theorem real_kernel_convolution_l2_integrable_ae {K : T → ℝ} {f : T → F}
    (hK : StronglyMeasurable K) (hKi : Integrable K ν)
    (hf : StronglyMeasurable f) (hf2 : MemLp f 2 ν) :
    ∀ᵐ t ∂ν, Integrable (fun s => K s • f (t-s)) ν := by
  exact young_bochner_smul_integrable_ae hK hf
    (p := 1) (q := 2) (r := 2) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by simpa using memLp_one_iff_integrable.mpr hKi) (by simpa using hf2)

#print axioms real_kernel_convolution_l2_memLp
#print axioms real_kernel_convolution_l2_norm_le
#print axioms real_kernel_convolution_l2_integral_le
#print axioms real_kernel_convolution_l2_integrable_ae
end TheoremT.Continuum
