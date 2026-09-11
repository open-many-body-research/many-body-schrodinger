import YoungConvolutionExists_v1
import ContinuumFoundation_v1

noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
namespace TheoremT.Continuum

theorem realKernel_convolution_memLp_two {N : ℕ} {K : Configuration N → ℝ}
    (hKm : StronglyMeasurable K) (hKi : Integrable K) (f : SpatialL2 N) :
    MemLp (fun x => ∫ y, K y • f (x-y)) 2 volume := by
  simpa only [ENNReal.ofReal_one,ENNReal.ofReal_ofNat] using
    young_bochner_smul_memLp hKm (Lp.stronglyMeasurable f)
      (p := 1) (q := 2) (r := 2) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by simpa using memLp_one_iff_integrable.mpr hKi) (by simpa using Lp.memLp f)

def realKernelConvolutionL2 {N : ℕ} (K : Configuration N → ℝ)
    (hKm : StronglyMeasurable K) (hKi : Integrable K) (f : SpatialL2 N) : SpatialL2 N :=
  (realKernel_convolution_memLp_two hKm hKi f).toLp (fun x => ∫ y, K y • f (x-y))

theorem realKernelConvolutionL2_ae {N : ℕ} (K : Configuration N → ℝ)
    (hKm : StronglyMeasurable K) (hKi : Integrable K) (f : SpatialL2 N) :
    (realKernelConvolutionL2 K hKm hKi f : Configuration N → ℂ) =ᵐ[volume]
      (fun x => ∫ y, K y • f (x-y)) :=
  (realKernel_convolution_memLp_two hKm hKi f).coeFn_toLp

theorem realKernel_convolution_integrable_ae {N : ℕ} {K : Configuration N → ℝ}
    (hKm : StronglyMeasurable K) (hKi : Integrable K) (f : SpatialL2 N) :
    ∀ᵐ x ∂volume, Integrable (fun y => K y • f (x-y)) := by
  exact young_bochner_smul_integrable_ae hKm (Lp.stronglyMeasurable f)
    (p := 1) (q := 2) (r := 2) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by simpa using memLp_one_iff_integrable.mpr hKi) (by simpa using Lp.memLp f)

theorem realKernelConvolutionL2_dist_le {N : ℕ} (K : Configuration N → ℝ)
    (hKm : StronglyMeasurable K) (hKi : Integrable K) (f g : SpatialL2 N) :
    dist (realKernelConvolutionL2 K hKm hKi f) (realKernelConvolutionL2 K hKm hKi g) ≤
      (eLpNorm K 1 volume).toReal * dist f g := by
  have he : (fun x => realKernelConvolutionL2 K hKm hKi f x - realKernelConvolutionL2 K hKm hKi g x)
      =ᵐ[volume] (fun x => ∫ y, K y • (f (x-y)-g (x-y))) := by
    filter_upwards [realKernelConvolutionL2_ae K hKm hKi f, realKernelConvolutionL2_ae K hKm hKi g,
      realKernel_convolution_integrable_ae hKm hKi f,
      realKernel_convolution_integrable_ae hKm hKi g] with x hxf hxg hif hig
    rw [hxf,hxg,← integral_sub hif hig]
    simp only [smul_sub]
  have hb : eLpNorm (fun x => ∫ y, K y • (f (x-y)-g (x-y))) 2 volume ≤
      eLpNorm K 1 volume * eLpNorm (fun x => f x-g x) 2 volume := by
    simpa only [ENNReal.ofReal_one,ENNReal.ofReal_ofNat,Pi.sub_apply] using
      young_bochner_smul_eLpNorm_le (f := fun x => f x-g x) hKm
        ((Lp.stronglyMeasurable f).sub (Lp.stronglyMeasurable g))
        (p := 1) (q := 2) (r := 2) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num)
  rw [Lp.dist_def]
  change (eLpNorm (fun x => realKernelConvolutionL2 K hKm hKi f x - realKernelConvolutionL2 K hKm hKi g x) 2 volume).toReal ≤ _
  rw [eLpNorm_congr_ae he, Lp.dist_def, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top (memLp_one_iff_integrable.mpr hKi).eLpNorm_ne_top
    ((Lp.memLp f).sub (Lp.memLp g)).eLpNorm_ne_top) hb

theorem realKernelConvolutionL2_continuous {N : ℕ} (K : Configuration N → ℝ)
    (hKm : StronglyMeasurable K) (hKi : Integrable K) :
    Continuous (realKernelConvolutionL2 K hKm hKi) := by
  have h : LipschitzWith (eLpNorm K 1 volume).toNNReal (realKernelConvolutionL2 K hKm hKi) := by
    apply LipschitzWith.of_dist_le_mul
    intro f g
    exact realKernelConvolutionL2_dist_le K hKm hKi f g
  exact h.continuous

#print axioms realKernelConvolutionL2_continuous
end TheoremT.Continuum
