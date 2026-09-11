import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ContDiff.Operations

noncomputable section
open MeasureTheory
namespace TheoremT.Continuum
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

theorem compact_real_directional_integral_zero {u : E → ℝ}
    (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u) (v : E) :
    (∫ x, fderiv ℝ u x v ∂μ)=0 := by
  have hd : Continuous (fun x => fderiv ℝ u x v) :=
    (hu.continuous_fderiv_apply (by norm_num)).comp (continuous_id.prodMk continuous_const)
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := μ)
    (f := u) (g := fun _ => (1:ℝ)) (v := v)
    (by simpa only [mul_one] using hd.integrable_of_hasCompactSupport (hc.fderiv_apply ℝ v))
    (by simp)
    (by simpa only [mul_one] using hu.continuous.integrable_of_hasCompactSupport hc)
    (fun x _ => hu.differentiable (by norm_num) x)
    (fun x _ => differentiableAt_const _)
  simpa using h.symm

#print axioms compact_real_directional_integral_zero
end TheoremT.Continuum
