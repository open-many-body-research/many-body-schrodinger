import CompactPartialFourier_v1
import CompactPartialIntegralDirectional_v1

noncomputable section
open MeasureTheory
open scoped ContDiff FourierTransform
namespace TheoremT.Continuum
variable {Y T : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T]
  [MeasurableSpace T] [BorelSpace T] [FiniteDimensional ℝ T]

theorem partialFourierIntegrand_yDirectional {G : Y × T → ℂ}
    (hG : ContDiff ℝ ∞ G) (ξ : T) (v : Y) :
    partialYDirectional (partialFourierIntegrand G ξ) v =
      partialFourierIntegrand (partialYDirectional G v) ξ := by
  funext p
  have h1 := firstParameterFDeriv_hasFDerivAt (partialFourierIntegrand_contDiff hG ξ) p.1 p.2
  have h2 := (firstParameterFDeriv_hasFDerivAt hG p.1 p.2).const_mul (partialFourierKernel ξ p.2)
  have he := h1.unique h2
  have hv := congrArg (fun L : Y →L[ℝ] ℂ => L v) he
  simpa [partialYDirectional,firstParameterFDeriv,partialFourierIntegrand,
    ContinuousLinearMap.comp_apply] using hv

theorem partialFourier_yDirectional {G : Y × T → ℂ} (hG : ContDiff ℝ ∞ G)
    (hc : HasCompactSupport G) (ξ : T) (y v : Y) :
    fderiv ℝ (partialFourier G ξ) y v = partialFourier (partialYDirectional G v) ξ y := by
  rw [partialFourier_eq_partialIntegral]
  rw [compactPartialIntegral_directional (partialFourierIntegrand_contDiff hG ξ)
    (partialFourierIntegrand_hasCompactSupport hc ξ)]
  rw [partialFourierIntegrand_yDirectional hG]
  exact congrFun (partialFourier_eq_partialIntegral (partialYDirectional G v) ξ).symm y

#print axioms partialFourierIntegrand_yDirectional
#print axioms partialFourier_yDirectional
end TheoremT.Continuum
