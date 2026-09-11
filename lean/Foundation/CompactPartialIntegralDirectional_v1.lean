import CompactPartialIntegralDerivative_v1

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum
variable {Y T F : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup T] [NormedSpace ℝ T]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [MeasurableSpace T] [BorelSpace T] {μ : Measure T} [IsFiniteMeasureOnCompacts μ]

def partialYDirectional (G : Y × T → F) (v : Y) (p : Y × T) : F :=
  fderiv ℝ G p (v,0)

theorem partialYDirectional_contDiff {G : Y × T → F} (hG : ContDiff ℝ ∞ G) (v : Y) :
    ContDiff ℝ ∞ (partialYDirectional G v) :=
  (hG.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const

theorem partialYDirectional_hasCompactSupport {G : Y × T → F}
    (hc : HasCompactSupport G) (v : Y) : HasCompactSupport (partialYDirectional G v) :=
  hc.fderiv_apply ℝ (v,0)

theorem compactPartialIntegral_directional {G : Y × T → F}
    (hG : ContDiff ℝ ∞ G) (hc : HasCompactSupport G) (y v : Y) :
    fderiv ℝ (compactPartialIntegral (μ := μ) G) y v =
      compactPartialIntegral (μ := μ) (partialYDirectional G v) y := by
  rw [compactPartialIntegral_fderiv hG hc]
  exact ContinuousLinearMap.integral_apply
    (compact_slice_integrable (firstParameterFDeriv_contDiff hG).continuous
      (firstParameterFDeriv_hasCompactSupport hc) y) v

#print axioms partialYDirectional_contDiff
#print axioms partialYDirectional_hasCompactSupport
#print axioms compactPartialIntegral_directional
end TheoremT.Continuum
