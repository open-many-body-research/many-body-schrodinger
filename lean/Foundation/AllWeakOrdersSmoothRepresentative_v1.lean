import L1FourierDistribution_v1
import SobolevFourierMoments_v1
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.FourierTransformDeriv

noncomputable section
open MeasureTheory FourierTransform
open scoped SchwartzMap ContDiff
namespace TheoremT.Continuum

theorem continuous_integrable_rep_contDiff_of_all_weak_orders {N : ℕ}
    (f : SpatialL2 N) (hf : ∀ n : ℕ, HasWeakOrder f n)
    {g : Configuration N → ℂ} (hg : Continuous g) (hgi : Integrable g)
    (hfg : (f : Configuration N → ℂ) =ᵐ[volume] g) : ContDiff ℝ ∞ g := by
  have hfi : Integrable (f : Configuration N → ℂ) := hgi.congr hfg.symm
  have hF : 𝓕 g =ᵐ[volume] (𝓕 f : SpatialL2 N) := by
    filter_upwards [actual_fourier_ae_L2_fourier f hfi] with x hx
    exact (Real.fourier_congr_ae hfg x).symm.trans hx
  have hM (n : ℕ) : Integrable (fun x : Configuration N => ‖x‖^n * ‖𝓕 g x‖) := by
    apply (all_weak_orders_fourier_moments f hf n).congr
    filter_upwards [hF] with x hx
    rw [hx]
  have hFc : Continuous (𝓕 g) := by
    simpa only [Real.fourierTransform_toLp] using
      (Real.Lp.fourierTransform (memLp_one_iff_integrable.mpr hgi).toLp).continuous
  have hFi : Integrable (𝓕 g) := by
    apply (integrable_norm_iff hFc.aestronglyMeasurable).mp
    simpa using hM 0
  have hd : ContDiff ℝ ∞ (𝓕 (𝓕 g)) := Real.contDiff_fourier (fun n _ => hM n)
  have hdi : ContDiff ℝ ∞ (𝓕⁻ (𝓕 g)) := by
    have he : 𝓕⁻ (𝓕 g) = fun x : Configuration N => 𝓕 (𝓕 g) (-x) :=
      funext (Real.fourierInv_eq_fourier_neg (𝓕 g))
    rw [he]
    exact hd.comp contDiff_neg
  rwa [hg.fourierInv_fourier_eq hgi hFi] at hdi

#print axioms continuous_integrable_rep_contDiff_of_all_weak_orders
end TheoremT.Continuum
