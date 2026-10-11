import FourierProductIdentification_v1
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Distribution.FourierMultiplier

/-!
Pointwise L2 Fourier identities from actual distributional derivative outputs.
The unbounded multiplier's L2 membership is a conclusion, never a premise.
The convention is exp(-2*pi*i*inner), exactly as in the pinned mathlib.
-/

noncomputable section
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian

namespace TheoremT.Continuum

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem fourier_derivative_distribution_output
    (f g : Lp ℂ 2 (volume : Measure E)) (v : E)
    (h : ∂_{v} (f : 𝓢'(E, ℂ)) = (g : 𝓢'(E, ℂ))) :
    ((𝓕 g : Lp ℂ 2 (volume : Measure E)) : 𝓢'(E, ℂ)) = smulLeftCLM ℂ
      (fun x : E => (2 * Real.pi * Complex.I) * (inner ℝ x v : ℂ))
      ((𝓕 f : Lp ℂ 2 (volume : Measure E)) : 𝓢'(E, ℂ)) := by
  have hgrowth : (fun x : E => (inner ℝ x v : ℂ)).HasTemperateGrowth := by
    fun_prop
  have hF := congrArg (fun T : 𝓢'(E, ℂ) => 𝓕 T) h
  rw [fourier_lineDerivOp_eq, Lp.fourier_toTemperedDistribution_eq,
    Lp.fourier_toTemperedDistribution_eq] at hF
  have hmult :
      smulLeftCLM ℂ (fun x : E =>
        (2 * Real.pi * Complex.I) * (inner ℝ x v : ℂ)) =
        (2 * Real.pi * Complex.I) •
          smulLeftCLM ℂ (fun x : E => (inner ℝ x v : ℂ)) := by
    exact smulLeftCLM_smul hgrowth (2 * Real.pi * Complex.I)
  rw [hmult]
  exact hF.symm

theorem fourier_derivative_ae
    (f g : Lp ℂ 2 (volume : Measure E)) (v : E)
    (h : ∂_{v} (f : 𝓢'(E, ℂ)) = (g : 𝓢'(E, ℂ))) :
    ∀ᵐ x ∂volume, (𝓕 g) x =
      ((2 * Real.pi * Complex.I) * (inner ℝ x v : ℂ)) * (𝓕 f) x := by
  exact ae_smul_eq_of_toTemperedDistribution_eq (𝓕 f) (𝓕 g)
    (by fun_prop) (fourier_derivative_distribution_output f g v h)

theorem fourier_derivative_product_memLp
    (f g : Lp ℂ 2 (volume : Measure E)) (v : E)
    (h : ∂_{v} (f : 𝓢'(E, ℂ)) = (g : 𝓢'(E, ℂ))) :
    MemLp (fun x : E =>
      ((2 * Real.pi * Complex.I) * (inner ℝ x v : ℂ)) * (𝓕 f) x) 2 volume := by
  exact memLp_smul_of_toTemperedDistribution_eq (𝓕 f) (𝓕 g)
    (by fun_prop) (fourier_derivative_distribution_output f g v h)

#print axioms fourier_derivative_distribution_output
#print axioms fourier_derivative_ae
#print axioms fourier_derivative_product_memLp

end TheoremT.Continuum
