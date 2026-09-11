import CompactPartialIntegralSmooth_v1
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section
open MeasureTheory
open scoped ContDiff RealInnerProductSpace FourierTransform
namespace TheoremT.Continuum
variable {Y T : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T]
  [MeasurableSpace T] [BorelSpace T] [FiniteDimensional ℝ T]

def partialFourier (G : Y × T → ℂ) (ξ : T) (y : Y) : ℂ :=
  𝓕 (fun t => G (y,t)) ξ

def partialFourierKernel (ξ : T) (t : T) : ℂ :=
  Complex.exp ((↑(-2*Real.pi*⟪t,ξ⟫) : ℂ)*Complex.I)

def partialFourierIntegrand (G : Y × T → ℂ) (ξ : T) (p : Y × T) : ℂ :=
  partialFourierKernel ξ p.2 * G p

theorem partialFourierKernel_contDiff (ξ : T) : ContDiff ℝ ∞ (partialFourierKernel ξ) := by
  have hR : ContDiff ℝ ∞ (fun t : T => -2*Real.pi*⟪t,ξ⟫) :=
    contDiff_const.mul ((innerSL ℝ).flip ξ).contDiff
  exact ((Complex.ofRealCLM.contDiff.comp hR).mul contDiff_const).cexp

theorem partialFourierIntegrand_contDiff {G : Y × T → ℂ} (hG : ContDiff ℝ ∞ G) (ξ : T) :
    ContDiff ℝ ∞ (partialFourierIntegrand G ξ) :=
  ((partialFourierKernel_contDiff ξ).comp contDiff_snd).mul hG

theorem partialFourierIntegrand_hasCompactSupport {G : Y × T → ℂ}
    (hc : HasCompactSupport G) (ξ : T) : HasCompactSupport (partialFourierIntegrand G ξ) :=
  hc.mul_left

theorem partialFourier_eq_partialIntegral (G : Y × T → ℂ) (ξ : T) :
    partialFourier G ξ = compactPartialIntegral (μ := volume) (partialFourierIntegrand G ξ) := by
  funext y
  exact Real.fourier_eq' (fun t => G (y,t)) ξ

theorem partialFourier_contDiff {G : Y × T → ℂ} (hG : ContDiff ℝ ∞ G)
    (hc : HasCompactSupport G) (ξ : T) : ContDiff ℝ ∞ (partialFourier G ξ) := by
  rw [partialFourier_eq_partialIntegral]
  exact compactPartialIntegral_contDiff (partialFourierIntegrand_contDiff hG ξ)
    (partialFourierIntegrand_hasCompactSupport hc ξ)

theorem partialFourier_hasCompactSupport {G : Y × T → ℂ}
    (hc : HasCompactSupport G) (ξ : T) : HasCompactSupport (partialFourier G ξ) := by
  rw [partialFourier_eq_partialIntegral]
  exact compactPartialIntegral_hasCompactSupport (partialFourierIntegrand_hasCompactSupport hc ξ)

#print axioms partialFourier_eq_partialIntegral
#print axioms partialFourier_contDiff
#print axioms partialFourier_hasCompactSupport
end TheoremT.Continuum
