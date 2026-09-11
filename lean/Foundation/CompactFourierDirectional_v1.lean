import CompactPartialFourierPlancherelSlice_v1

noncomputable section
open MeasureTheory
open scoped ContDiff FourierTransform RealInnerProductSpace
namespace TheoremT.Continuum
variable {T : Type} [NormedAddCommGroup T] [InnerProductSpace ℝ T]
  [MeasurableSpace T] [BorelSpace T] [FiniteDimensional ℝ T]

theorem compact_fourier_directional {f : T → ℂ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (ξ v : T) :
    𝓕 (fun t => fderiv ℝ f t v) ξ =
      (2*Real.pi*Complex.I)*(⟪ξ,v⟫ : ℂ)*𝓕 f ξ := by
  have hI := hf.continuous.integrable_of_hasCompactSupport hc (μ := volume)
  have hD := (hf.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).continuous.integrable_of_hasCompactSupport
    (hc.fderiv ℝ) (μ := volume)
  rw [← Real.fourier_continuousLinearMap_apply hD,Real.fourier_fderiv hI (hf.differentiable (by simp)) hD]
  simp only [VectorFourier.fourierSMulRight_apply,ContinuousLinearMap.neg_apply,
    innerSL_apply_apply ℝ,Complex.real_smul,mul_assoc,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smul_apply,neg_smul,smul_neg,Complex.ofReal_neg,neg_neg,
    Complex.coe_smul,smul_eq_mul]
  ring

#print axioms compact_fourier_directional
end TheoremT.Continuum
