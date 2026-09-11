import FourierProductIdentification_v1
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Distribution.FourierMultiplier

/-! Actual a.e. L2 Fourier representation of a distributional L2 Laplacian.
No integrability of the unbounded polynomial multiplier is assumed. -/

noncomputable section
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap Laplacian

namespace TheoremT.Continuum

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem fourier_laplacian_distribution_output
    (f w : Lp ℂ 2 (volume : Measure E))
    (h : Δ (f : 𝓢'(E, ℂ)) = (w : 𝓢'(E, ℂ))) :
    ((𝓕 w : Lp ℂ 2 (volume : Measure E)) : 𝓢'(E, ℂ)) = smulLeftCLM ℂ
      (fun x : E => (-(2 * Real.pi) ^ 2 : ℝ) * (‖x‖ ^ 2 : ℝ))
      ((𝓕 f : Lp ℂ 2 (volume : Measure E)) : 𝓢'(E, ℂ)) := by
  let c : ℂ := ((-(2 * Real.pi) ^ 2 : ℝ) : ℂ)
  have hgrowth : (fun x : E => Complex.ofReal (‖x‖ ^ 2)).HasTemperateGrowth := by
    fun_prop
  have hlap : Δ (f : 𝓢'(E, ℂ)) =
      c • fourierMultiplierCLM ℂ (fun x : E => Complex.ofReal (‖x‖ ^ 2))
        (f : 𝓢'(E, ℂ)) := by
    simpa only [c, Complex.coe_smul] using
      laplacian_eq_fourierMultiplierCLM (f : 𝓢'(E, ℂ))
  have hF := congrArg (fun T : 𝓢'(E, ℂ) => 𝓕 T) h
  rw [hlap, fourier_smul, fourierMultiplierCLM_apply,
    fourier_fourierInv_eq, Lp.fourier_toTemperedDistribution_eq,
    Lp.fourier_toTemperedDistribution_eq] at hF
  have hfun : (fun x : E => ((-(2 * Real.pi) ^ 2 : ℝ) * (‖x‖ ^ 2 : ℝ) : ℂ)) =
      c • (fun x : E => Complex.ofReal (‖x‖ ^ 2)) := by
    ext x
    simp [c]
  rw [hfun, smulLeftCLM_smul hgrowth c]
  exact hF.symm

theorem fourier_laplacian_ae
    (f w : Lp ℂ 2 (volume : Measure E))
    (h : Δ (f : 𝓢'(E, ℂ)) = (w : 𝓢'(E, ℂ))) :
    ∀ᵐ x ∂volume, (𝓕 w) x =
      ((-(2 * Real.pi) ^ 2 : ℝ) * (‖x‖ ^ 2 : ℝ) : ℂ) * (𝓕 f) x := by
  exact ae_smul_eq_of_toTemperedDistribution_eq (𝓕 f) (𝓕 w)
    (by fun_prop) (fourier_laplacian_distribution_output f w h)

theorem fourier_laplacian_product_memLp
    (f w : Lp ℂ 2 (volume : Measure E))
    (h : Δ (f : 𝓢'(E, ℂ)) = (w : 𝓢'(E, ℂ))) :
    MemLp (fun x : E =>
      ((-(2 * Real.pi) ^ 2 : ℝ) * (‖x‖ ^ 2 : ℝ) : ℂ) * (𝓕 f) x) 2 volume := by
  exact memLp_smul_of_toTemperedDistribution_eq (𝓕 f) (𝓕 w)
    (by fun_prop) (fourier_laplacian_distribution_output f w h)

#print axioms fourier_laplacian_distribution_output
#print axioms fourier_laplacian_ae
#print axioms fourier_laplacian_product_memLp

end TheoremT.Continuum
