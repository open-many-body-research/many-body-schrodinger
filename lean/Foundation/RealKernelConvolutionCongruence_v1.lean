import RealKernelConvolutionL2_v1
import Mathlib.MeasureTheory.Group.Integral

noncomputable section
open MeasureTheory MeasureTheory.Measure Filter
namespace TheoremT.Continuum

theorem realKernel_convolution_congr_ae_input {N : ℕ} (K : Configuration N → ℝ)
    {f g : Configuration N → ℂ} (hfg : f =ᵐ[volume] g) (x : Configuration N) :
    (∫ y, K y • f (x-y)) = ∫ y, K y • g (x-y) := by
  apply integral_congr_ae
  filter_upwards [(measurePreserving_sub_left volume x).quasiMeasurePreserving.ae hfg] with y hy
  rw [hy]

theorem realKernelConvolutionL2_ae_representative {N : ℕ} (K : Configuration N → ℝ)
    (hKm : StronglyMeasurable K) (hKi : Integrable K) (f : SpatialL2 N)
    {g : Configuration N → ℂ} (hfg : (f : Configuration N → ℂ) =ᵐ[volume] g) :
    (realKernelConvolutionL2 K hKm hKi f : Configuration N → ℂ) =ᵐ[volume]
      (fun x => ∫ y, K y • g (x-y)) := by
  filter_upwards [realKernelConvolutionL2_ae K hKm hKi f] with x hx
  rw [hx,realKernel_convolution_congr_ae_input K hfg x]

#print axioms realKernelConvolutionL2_ae_representative
end TheoremT.Continuum
