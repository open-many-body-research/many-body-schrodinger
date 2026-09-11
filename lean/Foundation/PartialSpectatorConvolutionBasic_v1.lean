import RealKernelConvolutionL2Generic_v1
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped ENNReal
namespace TheoremT.Continuum
variable {Y T F : Type*} [MeasurableSpace Y] [MeasurableSpace T] [AddCommGroup T]
  [MeasurableAdd₂ T] [MeasurableNeg T] {μ : Measure Y} {ν : Measure T} [SFinite μ] [SFinite ν]
  [IsAddRightInvariant ν] [IsAddLeftInvariant ν] [IsNegInvariant ν]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

def partialSpectatorConvolution (K : T → ℝ) (G : Y × T → F) (p : Y × T) : F :=
  ∫ s, K s • G (p.1,p.2-s) ∂ν

theorem partialSpectatorConvolution_integrand_stronglyMeasurable
    {K : T → ℝ} {G : Y × T → F} (hK : StronglyMeasurable K) (hG : StronglyMeasurable G) :
    StronglyMeasurable (fun q : (Y × T) × T => K q.2 • G (q.1.1,q.1.2-q.2)) :=
  (hK.comp_measurable measurable_snd).smul
    (hG.comp_measurable (measurable_fst.fst.prodMk (measurable_fst.snd.sub measurable_snd)))

theorem partialSpectatorConvolution_stronglyMeasurable
    {K : T → ℝ} {G : Y × T → F} (hK : StronglyMeasurable K) (hG : StronglyMeasurable G) :
    StronglyMeasurable (partialSpectatorConvolution (ν := ν) K G) :=
  (partialSpectatorConvolution_integrand_stronglyMeasurable hK hG).integral_prod_right'

theorem memLp_two_product_slices {G : Y × T → F}
    (hG : StronglyMeasurable G) (hG2 : MemLp G 2 (μ.prod ν)) :
    ∀ᵐ y ∂μ, MemLp (fun t => G (y,t)) 2 ν := by
  have hI := hG2.integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)
  filter_upwards [hI.prod_right_ae] with y hy
  exact (memLp_two_iff_integrable_sq_norm
    (hG.comp_measurable measurable_prodMk_left).aestronglyMeasurable).mpr hy

theorem partialSpectatorConvolution_integrable_ae_slices
    {K : T → ℝ} {G : Y × T → F} (hK : StronglyMeasurable K) (hKi : Integrable K ν)
    (hG : StronglyMeasurable G) (hG2 : MemLp G 2 (μ.prod ν)) :
    ∀ᵐ y ∂μ, ∀ᵐ t ∂ν, Integrable (fun s : T => K s • G (y,t-s)) ν := by
  filter_upwards [memLp_two_product_slices hG hG2] with y hy
  have hslice : StronglyMeasurable (fun t : T => G (y,t)) :=
    hG.comp_measurable measurable_prodMk_left
  exact real_kernel_convolution_l2_integrable_ae (ν := ν) (K := K) (f := fun t : T => G (y,t))
    hK hKi hslice hy

theorem partialSpectatorConvolution_integrable_ae
    {K : T → ℝ} {G : Y × T → F} (hK : StronglyMeasurable K) (hKi : Integrable K ν)
    (hG : StronglyMeasurable G) (hG2 : MemLp G 2 (μ.prod ν)) :
    ∀ᵐ p ∂μ.prod ν, Integrable (fun s => K s • G (p.1,p.2-s)) ν := by
  have hset : MeasurableSet {p : Y × T | Integrable (fun s => K s • G (p.1,p.2-s)) ν} :=
    measurableSet_integrable (μ := ν) (f := fun (p : Y × T) (s : T) => K s • G (p.1,p.2-s))
      (partialSpectatorConvolution_integrand_stronglyMeasurable hK hG)
  apply (ae_prod_iff_ae_ae hset).mpr
  exact partialSpectatorConvolution_integrable_ae_slices hK hKi hG hG2

theorem partialSpectatorConvolution_ae_congr
    {K : T → ℝ} {G H : Y × T → F} (hK : StronglyMeasurable K)
    (hG : StronglyMeasurable G) (hH : StronglyMeasurable H) (he : G =ᵐ[μ.prod ν] H) :
    partialSpectatorConvolution (ν := ν) K G =ᵐ[μ.prod ν]
      partialSpectatorConvolution (ν := ν) K H := by
  apply (ae_prod_iff_ae_ae
    ((partialSpectatorConvolution_stronglyMeasurable hK hG).measurableSet_eq_fun
      (partialSpectatorConvolution_stronglyMeasurable hK hH))).mpr
  filter_upwards [ae_ae_of_ae_prod he] with y hy
  apply Filter.Eventually.of_forall
  intro t
  apply integral_congr_ae
  filter_upwards [(measurePreserving_sub_left ν t).quasiMeasurePreserving.ae_eq_comp hy] with s hs
  exact congrArg (fun z : F => K s • z) hs

#print axioms partialSpectatorConvolution
#print axioms partialSpectatorConvolution_integrand_stronglyMeasurable
#print axioms partialSpectatorConvolution_stronglyMeasurable
#print axioms memLp_two_product_slices
#print axioms partialSpectatorConvolution_integrable_ae_slices
#print axioms partialSpectatorConvolution_integrable_ae
#print axioms partialSpectatorConvolution_ae_congr
end TheoremT.Continuum
