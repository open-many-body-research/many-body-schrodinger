import PartialSpectatorConvolutionAEL2_v1
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Measure.Haar.Unique

noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped ContDiff Convolution
namespace TheoremT.Continuum
variable {Y T F : Type*} [MeasurableSpace Y] {μ : Measure Y} [SFinite μ]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T]
  [MeasurableSpace T] [BorelSpace T] {ν : Measure T} [IsAddHaarMeasure ν]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

def spectatorFiberDirectional (G : Y × T → F) (v : T) (p : Y × T) : F :=
  fderiv ℝ (fun t => G (p.1,t)) p.2 v

theorem memLp_two_product_slices_ae {G : Y × T → F} (hG2 : MemLp G 2 (μ.prod ν)) :
    ∀ᵐ y ∂μ, MemLp (fun t => G (y,t)) 2 ν := by
  have he := hG2.aestronglyMeasurable.ae_eq_mk
  have hm := memLp_two_product_slices hG2.aestronglyMeasurable.stronglyMeasurable_mk (hG2.ae_eq he)
  filter_upwards [hm,ae_ae_of_ae_prod he] with y hy he
  exact hy.ae_eq (Filter.EventuallyEq.symm he)

theorem partialSpectatorConvolution_smooth_fiber_ae
    {K : T → ℝ} {G : Y × T → F} (hK : ContDiff ℝ ∞ K) (hcK : HasCompactSupport K)
    (hG2 : MemLp G 2 (μ.prod ν)) :
    ∀ᵐ y ∂μ, ContDiff ℝ ∞ (fun t => partialSpectatorConvolution (ν := ν) K G (y,t)) := by
  filter_upwards [memLp_two_product_slices_ae hG2] with y hy
  exact hcK.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hK
    (hy.locallyIntegrable (by norm_num))

theorem partialSpectatorConvolution_fiber_derivative_of_slice
    {K : T → ℝ} {G : Y × T → F} (hK : ContDiff ℝ ∞ K) (hcK : HasCompactSupport K)
    (y : Y) (hy : MemLp (fun t => G (y,t)) 2 ν) (v t : T) :
    spectatorFiberDirectional (partialSpectatorConvolution (ν := ν) K G) v (y,t) =
      partialSpectatorConvolution (ν := ν) (fun s => fderiv ℝ K s v) G (y,t) := by
  let L : ℝ →L[ℝ] F →L[ℝ] F := ContinuousLinearMap.lsmul ℝ ℝ
  have hf := hy.locallyIntegrable (by norm_num)
  have hd := hcK.hasFDerivAt_convolution_left L (hK.of_le (by simp)) hf t
  unfold spectatorFiberDirectional
  change (fderiv ℝ (K ⋆[L,ν] (fun q => G (y,q))) t) v = _
  rw [hd.fderiv,convolution_def,ContinuousLinearMap.integral_apply]
  · rfl
  · exact (hcK.fderiv ℝ).convolutionExists_left (L.precompL T)
      (hK.continuous_fderiv (by simp)) hf t

theorem partialSpectatorConvolution_fiber_derivative_ae
    {K : T → ℝ} {G : Y × T → F} (hK : ContDiff ℝ ∞ K) (hcK : HasCompactSupport K)
    (hG2 : MemLp G 2 (μ.prod ν)) (v : T) :
    spectatorFiberDirectional (partialSpectatorConvolution (ν := ν) K G) v =ᵐ[μ.prod ν]
      partialSpectatorConvolution (ν := ν) (fun s => fderiv ℝ K s v) G := by
  filter_upwards [(quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae
    (memLp_two_product_slices_ae hG2)] with p hp
  exact partialSpectatorConvolution_fiber_derivative_of_slice hK hcK p.1 hp v p.2

#print axioms spectatorFiberDirectional
#print axioms memLp_two_product_slices_ae
#print axioms partialSpectatorConvolution_smooth_fiber_ae
#print axioms partialSpectatorConvolution_fiber_derivative_of_slice
#print axioms partialSpectatorConvolution_fiber_derivative_ae
end TheoremT.Continuum
