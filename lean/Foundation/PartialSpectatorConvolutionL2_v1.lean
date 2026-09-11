import PartialSpectatorConvolutionBasic_v1

noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped ENNReal
namespace TheoremT.Continuum
variable {Y T F : Type*} [MeasurableSpace Y] [MeasurableSpace T] [AddCommGroup T]
  [MeasurableAdd₂ T] [MeasurableNeg T] {μ : Measure Y} {ν : Measure T} [SFinite μ] [SFinite ν]
  [IsAddRightInvariant ν] [IsAddLeftInvariant ν] [IsNegInvariant ν]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem partialSpectatorConvolution_slice_integral_le_ae
    {K : T → ℝ} {G : Y × T → F} (hK : StronglyMeasurable K) (hKi : Integrable K ν)
    (hG : StronglyMeasurable G) (hG2 : MemLp G 2 (μ.prod ν)) :
    ∀ᵐ y ∂μ, (∫ t,‖partialSpectatorConvolution (ν := ν) K G (y,t)‖^2 ∂ν) ≤
      (∫ s,‖K s‖ ∂ν)^2*(∫ t,‖G (y,t)‖^2 ∂ν) := by
  filter_upwards [memLp_two_product_slices hG hG2] with y hy
  have hslice : StronglyMeasurable (fun t : T => G (y,t)) := hG.comp_measurable measurable_prodMk_left
  exact real_kernel_convolution_l2_integral_le (ν := ν) (K := K) (f := fun t : T => G (y,t))
    hK hKi hslice hy

theorem partialSpectatorConvolution_memLp_two
    {K : T → ℝ} {G : Y × T → F} (hK : StronglyMeasurable K) (hKi : Integrable K ν)
    (hG : StronglyMeasurable G) (hG2 : MemLp G 2 (μ.prod ν)) :
    MemLp (partialSpectatorConvolution (ν := ν) K G) 2 (μ.prod ν) := by
  have hHM := partialSpectatorConvolution_stronglyMeasurable (ν := ν) hK hG
  have hHM2 : StronglyMeasurable (fun p => ‖partialSpectatorConvolution (ν := ν) K G p‖^2) :=
    hHM.norm.pow 2
  apply (memLp_two_iff_integrable_sq_norm hHM.aestronglyMeasurable).mpr
  apply (integrable_prod_iff hHM2.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [memLp_two_product_slices hG hG2] with y hy
    exact (real_kernel_convolution_l2_memLp (ν := ν) (K := K) (f := fun t : T => G (y,t)) hK hKi
      (hG.comp_measurable measurable_prodMk_left) hy).integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)
  · have hGI := hG2.integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)
    have hC := hGI.integral_prod_left.const_mul ((∫ s,‖K s‖ ∂ν)^2)
    have hInt : Integrable (fun y => ∫ t,‖partialSpectatorConvolution (ν := ν) K G (y,t)‖^2 ∂ν) μ :=
      hC.mono_nonneg hHM2.integral_prod_right'.aestronglyMeasurable
        (Filter.Eventually.of_forall (fun y => integral_nonneg (fun t => sq_nonneg _)))
        (partialSpectatorConvolution_slice_integral_le_ae hK hKi hG hG2)
    simpa only [norm_pow,norm_norm] using hInt

theorem partialSpectatorConvolution_integral_sq_le
    {K : T → ℝ} {G : Y × T → F} (hK : StronglyMeasurable K) (hKi : Integrable K ν)
    (hG : StronglyMeasurable G) (hG2 : MemLp G 2 (μ.prod ν)) :
    (∫ p,‖partialSpectatorConvolution (ν := ν) K G p‖^2 ∂μ.prod ν) ≤
      (∫ s,‖K s‖ ∂ν)^2*(∫ p,‖G p‖^2 ∂μ.prod ν) := by
  have hHI := (partialSpectatorConvolution_memLp_two hK hKi hG hG2).integrable_norm_pow
    (by norm_num : (2:ℕ) ≠ 0)
  have hGI := hG2.integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)
  have h := integral_mono_ae hHI.integral_prod_left
    (hGI.integral_prod_left.const_mul ((∫ s,‖K s‖ ∂ν)^2))
    (partialSpectatorConvolution_slice_integral_le_ae hK hKi hG hG2)
  rw [integral_const_mul,← integral_prod _ hHI,← integral_prod _ hGI] at h
  exact h

theorem partialSpectatorConvolution_l2_norm_le
    {K : T → ℝ} {G : Y × T → F} (hK : StronglyMeasurable K) (hKi : Integrable K ν)
    (hG : StronglyMeasurable G) (hG2 : MemLp G 2 (μ.prod ν)) :
    ‖(partialSpectatorConvolution_memLp_two hK hKi hG hG2).toLp
      (partialSpectatorConvolution (ν := ν) K G)‖ ≤
      (∫ s,‖K s‖ ∂ν)*‖hG2.toLp G‖ := by
  have h := partialSpectatorConvolution_integral_sq_le hK hKi hG hG2
  rw [← actual_l2_toLp_norm_sq_integral (partialSpectatorConvolution_memLp_two hK hKi hG hG2),
    ← actual_l2_toLp_norm_sq_integral hG2] at h
  have hp := mul_nonneg (integral_nonneg (μ := ν) (fun s => norm_nonneg (K s))) (norm_nonneg (hG2.toLp G))
  nlinarith only [h,hp,norm_nonneg ((partialSpectatorConvolution_memLp_two hK hKi hG hG2).toLp
    (partialSpectatorConvolution (ν := ν) K G))]

#print axioms partialSpectatorConvolution_slice_integral_le_ae
#print axioms partialSpectatorConvolution_memLp_two
#print axioms partialSpectatorConvolution_integral_sq_le
#print axioms partialSpectatorConvolution_l2_norm_le
end TheoremT.Continuum
