import PartialSpectatorConvolutionL2_v1

noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped ENNReal
namespace TheoremT.Continuum
variable {Y T F : Type*} [MeasurableSpace Y] [MeasurableSpace T] [AddCommGroup T]
  [MeasurableAdd₂ T] [MeasurableNeg T] {μ : Measure Y} {ν : Measure T} [SFinite μ] [SFinite ν]
  [IsAddRightInvariant ν] [IsAddLeftInvariant ν] [IsNegInvariant ν]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem partialSpectatorConvolution_kernel_congr {K L : T → ℝ}
    (he : K =ᵐ[ν] L) (G : Y × T → F) :
    partialSpectatorConvolution (ν := ν) K G = partialSpectatorConvolution (ν := ν) L G := by
  funext p
  apply integral_congr_ae
  filter_upwards [he] with s hs
  rw [hs]

theorem partialSpectatorConvolution_integrableKernel_memLp_two
    {K : T → ℝ} {G : Y × T → F} (hKi : Integrable K ν)
    (hG : StronglyMeasurable G) (hG2 : MemLp G 2 (μ.prod ν)) :
    MemLp (partialSpectatorConvolution (ν := ν) K G) 2 (μ.prod ν) := by
  have he := hKi.aestronglyMeasurable.ae_eq_mk
  rw [partialSpectatorConvolution_kernel_congr he G]
  exact partialSpectatorConvolution_memLp_two hKi.aestronglyMeasurable.stronglyMeasurable_mk
    (hKi.congr he) hG hG2

theorem partialSpectatorConvolution_integrableKernel_integral_sq_le
    {K : T → ℝ} {G : Y × T → F} (hKi : Integrable K ν)
    (hG : StronglyMeasurable G) (hG2 : MemLp G 2 (μ.prod ν)) :
    (∫ p,‖partialSpectatorConvolution (ν := ν) K G p‖^2 ∂μ.prod ν) ≤
      (∫ s,‖K s‖ ∂ν)^2*(∫ p,‖G p‖^2 ∂μ.prod ν) := by
  have he := hKi.aestronglyMeasurable.ae_eq_mk
  have hN : (∫ s,‖K s‖ ∂ν) = ∫ s,‖hKi.aestronglyMeasurable.mk K s‖ ∂ν :=
    integral_congr_ae (he.fun_comp norm)
  rw [partialSpectatorConvolution_kernel_congr he G,hN]
  exact partialSpectatorConvolution_integral_sq_le hKi.aestronglyMeasurable.stronglyMeasurable_mk
    (hKi.congr he) hG hG2

theorem partialSpectatorConvolution_integrableKernel_norm_le
    {K : T → ℝ} {G : Y × T → F} (hKi : Integrable K ν)
    (hG : StronglyMeasurable G) (hG2 : MemLp G 2 (μ.prod ν)) :
    ‖(partialSpectatorConvolution_integrableKernel_memLp_two hKi hG hG2).toLp
      (partialSpectatorConvolution (ν := ν) K G)‖ ≤
      (∫ s,‖K s‖ ∂ν)*‖hG2.toLp G‖ := by
  have h := partialSpectatorConvolution_integrableKernel_integral_sq_le hKi hG hG2
  rw [← actual_l2_toLp_norm_sq_integral (partialSpectatorConvolution_integrableKernel_memLp_two hKi hG hG2),
    ← actual_l2_toLp_norm_sq_integral hG2] at h
  have hp := mul_nonneg (integral_nonneg (μ := ν) (fun s => norm_nonneg (K s))) (norm_nonneg (hG2.toLp G))
  nlinarith only [h,hp,norm_nonneg ((partialSpectatorConvolution_integrableKernel_memLp_two hKi hG hG2).toLp
    (partialSpectatorConvolution (ν := ν) K G))]

theorem partialSpectatorConvolution_integrableKernel_integrable_ae
    {K : T → ℝ} {G : Y × T → F} (hKi : Integrable K ν)
    (hG : StronglyMeasurable G) (hG2 : MemLp G 2 (μ.prod ν)) :
    ∀ᵐ p ∂μ.prod ν, Integrable (fun s => K s • G (p.1,p.2-s)) ν := by
  have he := hKi.aestronglyMeasurable.ae_eq_mk
  have hi := partialSpectatorConvolution_integrable_ae hKi.aestronglyMeasurable.stronglyMeasurable_mk
    (hKi.congr he) hG hG2
  filter_upwards [hi] with p hp
  apply hp.congr
  filter_upwards [he] with s hs
  rw [hs]

theorem partialSpectatorConvolution_integrableKernel_ae_congr
    {K : T → ℝ} {G H : Y × T → F} (hKi : Integrable K ν)
    (hG : StronglyMeasurable G) (hH : StronglyMeasurable H) (he : G =ᵐ[μ.prod ν] H) :
    partialSpectatorConvolution (ν := ν) K G =ᵐ[μ.prod ν]
      partialSpectatorConvolution (ν := ν) K H := by
  have hk := hKi.aestronglyMeasurable.ae_eq_mk
  rw [partialSpectatorConvolution_kernel_congr hk G,partialSpectatorConvolution_kernel_congr hk H]
  exact partialSpectatorConvolution_ae_congr hKi.aestronglyMeasurable.stronglyMeasurable_mk hG hH he

#print axioms partialSpectatorConvolution_kernel_congr
#print axioms partialSpectatorConvolution_integrableKernel_memLp_two
#print axioms partialSpectatorConvolution_integrableKernel_integral_sq_le
#print axioms partialSpectatorConvolution_integrableKernel_norm_le
#print axioms partialSpectatorConvolution_integrableKernel_integrable_ae
#print axioms partialSpectatorConvolution_integrableKernel_ae_congr
end TheoremT.Continuum
