import PartialSpectatorConvolutionIntegrableKernel_v1

noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped ENNReal
namespace TheoremT.Continuum
variable {Y T F : Type*} [MeasurableSpace Y] [MeasurableSpace T] [AddCommGroup T]
  [MeasurableAdd₂ T] [MeasurableNeg T] {μ : Measure Y} {ν : Measure T} [SFinite μ] [SFinite ν]
  [IsAddRightInvariant ν] [IsAddLeftInvariant ν] [IsNegInvariant ν]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem partialSpectatorConvolution_ae_integrand_congr
    {G H : Y × T → F} (he : G =ᵐ[μ.prod ν] H) :
    ∀ᵐ p ∂μ.prod ν, (fun s => G (p.1,p.2-s)) =ᵐ[ν] (fun s => H (p.1,p.2-s)) := by
  filter_upwards [(quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae (ae_ae_of_ae_prod he)] with p hp
  exact (measurePreserving_sub_left ν p.2).quasiMeasurePreserving.ae_eq_comp hp

theorem partialSpectatorConvolution_ae_congr_of_ae
    {K : T → ℝ} {G H : Y × T → F} (he : G =ᵐ[μ.prod ν] H) :
    partialSpectatorConvolution (ν := ν) K G =ᵐ[μ.prod ν]
      partialSpectatorConvolution (ν := ν) K H := by
  filter_upwards [partialSpectatorConvolution_ae_integrand_congr he] with p hp
  apply integral_congr_ae
  filter_upwards [hp] with s hs
  rw [hs]

theorem partialSpectatorConvolution_ae_memLp_two
    {K : T → ℝ} {G : Y × T → F} (hKi : Integrable K ν) (hG2 : MemLp G 2 (μ.prod ν)) :
    MemLp (partialSpectatorConvolution (ν := ν) K G) 2 (μ.prod ν) := by
  have he := hG2.aestronglyMeasurable.ae_eq_mk
  exact (partialSpectatorConvolution_integrableKernel_memLp_two hKi
    hG2.aestronglyMeasurable.stronglyMeasurable_mk (hG2.ae_eq he)).ae_eq
      (partialSpectatorConvolution_ae_congr_of_ae he).symm

theorem partialSpectatorConvolution_ae_integral_sq_le
    {K : T → ℝ} {G : Y × T → F} (hKi : Integrable K ν) (hG2 : MemLp G 2 (μ.prod ν)) :
    (∫ p,‖partialSpectatorConvolution (ν := ν) K G p‖^2 ∂μ.prod ν) ≤
      (∫ s,‖K s‖ ∂ν)^2*(∫ p,‖G p‖^2 ∂μ.prod ν) := by
  have he := hG2.aestronglyMeasurable.ae_eq_mk
  have hc := partialSpectatorConvolution_ae_congr_of_ae (K := K) he
  have hi := partialSpectatorConvolution_integrableKernel_integral_sq_le hKi
    hG2.aestronglyMeasurable.stronglyMeasurable_mk (hG2.ae_eq he)
  have ec := integral_congr_ae (hc.fun_comp (fun z : F => ‖z‖^2))
  have eg := integral_congr_ae (he.fun_comp (fun z : F => ‖z‖^2))
  simp only [Function.comp_apply] at ec eg
  rw [ec,eg]
  exact hi

theorem partialSpectatorConvolution_ae_norm_le
    {K : T → ℝ} {G : Y × T → F} (hKi : Integrable K ν) (hG2 : MemLp G 2 (μ.prod ν)) :
    ‖(partialSpectatorConvolution_ae_memLp_two hKi hG2).toLp
      (partialSpectatorConvolution (ν := ν) K G)‖ ≤
      (∫ s,‖K s‖ ∂ν)*‖hG2.toLp G‖ := by
  have h := partialSpectatorConvolution_ae_integral_sq_le hKi hG2
  rw [← actual_l2_toLp_norm_sq_integral (partialSpectatorConvolution_ae_memLp_two hKi hG2),
    ← actual_l2_toLp_norm_sq_integral hG2] at h
  have hp := mul_nonneg (integral_nonneg (μ := ν) (fun s => norm_nonneg (K s))) (norm_nonneg (hG2.toLp G))
  nlinarith only [h,hp,norm_nonneg ((partialSpectatorConvolution_ae_memLp_two hKi hG2).toLp
    (partialSpectatorConvolution (ν := ν) K G))]

theorem partialSpectatorConvolution_ae_integrable
    {K : T → ℝ} {G : Y × T → F} (hKi : Integrable K ν) (hG2 : MemLp G 2 (μ.prod ν)) :
    ∀ᵐ p ∂μ.prod ν, Integrable (fun s => K s • G (p.1,p.2-s)) ν := by
  have he := hG2.aestronglyMeasurable.ae_eq_mk
  have hi := partialSpectatorConvolution_integrableKernel_integrable_ae hKi
    hG2.aestronglyMeasurable.stronglyMeasurable_mk (hG2.ae_eq he)
  filter_upwards [hi,partialSpectatorConvolution_ae_integrand_congr he] with p hp he
  apply hp.congr
  filter_upwards [he] with s hs
  rw [hs]

#print axioms partialSpectatorConvolution_ae_integrand_congr
#print axioms partialSpectatorConvolution_ae_congr_of_ae
#print axioms partialSpectatorConvolution_ae_memLp_two
#print axioms partialSpectatorConvolution_ae_integral_sq_le
#print axioms partialSpectatorConvolution_ae_norm_le
#print axioms partialSpectatorConvolution_ae_integrable
end TheoremT.Continuum
