import LpDistributionIdentification_v1
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

noncomputable section
open MeasureTheory FourierTransform
open scoped SchwartzMap
namespace TheoremT.Continuum
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem integral_fourier_smul_of_integrable {f g : E → ℂ}
    (hf : Integrable f) (hg : Integrable g) :
    (∫ x, 𝓕 f x • g x) = ∫ x, f x • 𝓕 g x := by
  simpa using! VectorFourier.integral_fourierIntegral_smul_eq_flip
    (L := innerₗ E) Real.continuous_fourierChar continuous_inner hf hg

theorem L1_fourier_distribution (f : Lp ℂ 1 (volume : Measure E)) :
    𝓕 (f : 𝓢'(E,ℂ)) =
      ((Real.Lp.fourierTransform f).memLp_top.toLp (Real.Lp.fourierTransform f) :
        Lp ℂ ⊤ volume) := by
  ext φ
  rw [TemperedDistribution.fourier_apply]
  simp only [Lp.toTemperedDistribution_apply]
  calc
    (∫ x, (𝓕 φ) x • f x) = ∫ x, φ x • 𝓕 (f : E → ℂ) x := by
      simpa only [SchwartzMap.fourier_coe] using integral_fourier_smul_of_integrable φ.integrable (L1.integrable_coeFn f)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [(Real.Lp.fourierTransform f).memLp_top.coeFn_toLp] with x hx
      rw [hx,Real.Lp.fourierTransform_apply]

theorem actual_fourier_ae_L2_fourier (f : Lp ℂ 2 (volume : Measure E))
    (hf : Integrable (f : E → ℂ)) :
    𝓕 (f : E → ℂ) =ᵐ[volume] (𝓕 f : Lp ℂ 2 volume) := by
  let h1 := (memLp_one_iff_integrable.mpr hf)
  let f1 : Lp ℂ 1 volume := h1.toLp f
  let v := (Real.Lp.fourierTransform f1).memLp_top (μ := volume)
  have hid : (f1 : 𝓢'(E,ℂ))=(f : 𝓢'(E,ℂ)) := by
    ext φ
    simp only [Lp.toTemperedDistribution_apply]
    exact integral_congr_ae (h1.coeFn_toLp.mono (fun x hx => by simpa only [f1] using congrArg (fun z : ℂ => φ x • z) hx))
  have he : (v.toLp (Real.Lp.fourierTransform f1) : 𝓢'(E,ℂ))=
      ((𝓕 f : Lp ℂ 2 volume) : 𝓢'(E,ℂ)) := by
    rw [← L1_fourier_distribution f1,hid,Lp.fourier_toTemperedDistribution_eq]
  have hae := ae_eq_of_Lp_temperedDistribution_eq _ _ he
  filter_upwards [hae,v.coeFn_toLp] with x hx hv
  rw [hv,Real.Lp.fourierTransform_apply] at hx
  exact (Real.fourier_congr_ae h1.coeFn_toLp x).symm.trans hx

#print axioms actual_fourier_ae_L2_fourier
end TheoremT.Continuum
