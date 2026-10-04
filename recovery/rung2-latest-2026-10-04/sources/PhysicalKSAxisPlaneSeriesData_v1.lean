import SO2PolynomialSeriesInput_v1
import PhysicalKSAxisRetainedRadius_v1

/-! Actual plane/spectator polynomial inputs for the physical axis A/B
functions, on any positive retained radius inside the proved analytic axis
radius. Spatial SO(2) invariance remains a separate input to descent. -/
noncomputable section
set_option autoImplicit false
namespace TheoremT.Continuum
open WeakGrushin

def physicalKSAxisPlanePolynomialA (f : Space (Fin 3) → ℂ) (t0 : Position) :=
  so2SpectatorFamily (physicalKSAxisPolynomialA f t0)

def physicalKSAxisPlanePolynomialB (f : Space (Fin 3) → ℂ) (t0 : Position) :=
  so2SpectatorFamily (physicalKSAxisPolynomialB f t0)

theorem physicalKSAxisPlaneSeries_data
    {f : Space (Fin 3) → ℂ} {v : Position → Position → ℂ}
    {t0 : Position} {M A F0 W h : ℝ}
    (hq : PhysicalKSAxisPolynomialData f t0 M A F0 W)
    (hdata : PhysicalKSBoxAnalyticDescentDerivativeData f v t0 M A F0 W)
    (hA : 1 ≤ A) (hF0 : 0 ≤ F0) (hh : 0 < h) (hr : h ≤ physicalKSAnalyticAxisRadius M A) :
    SO2PolynomialSeriesInput (physicalKSAxisPlanePolynomialA f t0)
      (fun z => physicalKSAnalyticDescentA f t0 (physicalKSComplexAxisMap z))
      (16*physicalKSPointwiseAmplitude M A F0 W) h ∧
    SO2PolynomialSeriesInput (physicalKSAxisPlanePolynomialB f t0)
      (fun z => physicalKSAnalyticDescentB f t0 (physicalKSComplexAxisMap z))
      ((32*(7*physicalKSPointwiseRate M A)^2)*(16*physicalKSPointwiseAmplitude M A F0 W)) h := by
  obtain ⟨hqa,hqb,hla,hlb,hsa,hsb⟩ := hq
  have hp := physicalKSPointwiseAmplitude_nonneg (M := M) (W := W) hA hF0
  have hd : 0 ≤ 32*(7*physicalKSPointwiseRate M A)^2 := by positivity
  have hB := (physicalKSAxisSeriesRate_pos (M := M) hA).le
  have hBh := physicalKSAxisSeriesRate_mul_retainedRadius_le_one hA hr
  have hbd := (physicalKSAnalyticDescent_axis_analytic_bounded hdata hA).2.2
  constructor
  · apply so2PolynomialSeriesInput_of_joint_polynomials (physicalKSAxisPolynomialA f t0) _
      hqa (mul_nonneg (by norm_num) hp) hB (by linarith) hh hBh hla
    · intro z hz
      exact hsa z (geometric_rate_lt_one_of_lt_retained_radius hB hh hBh (norm_nonneg _) hz)
    · intro z hz
      exact (hbd z (hz.trans_le hr)).1
  · have hCM : 8*(physicalKSPointwiseAmplitude M A F0 W *
        (32*(7*physicalKSPointwiseRate M A)^2)) ≤
        (32*(7*physicalKSPointwiseRate M A)^2)*(16*physicalKSPointwiseAmplitude M A F0 W) := by
      nlinarith [mul_nonneg hp hd]
    apply so2PolynomialSeriesInput_of_joint_polynomials (physicalKSAxisPolynomialB f t0) _
      hqb (mul_nonneg (by norm_num) (mul_nonneg hp hd)) hB hCM hh hBh hlb
    · intro z hz
      exact hsb z (geometric_rate_lt_one_of_lt_retained_radius hB hh hBh (norm_nonneg _) hz)
    · intro z hz
      exact (hbd z (hz.trans_le hr)).2

theorem nuclearKSPhysicalAxisPlaneSeries_data
    (g : Configuration 2 → ℂ) (i : Fin 2) {t0 : Position} {M A F0 W h : ℝ}
    (hdata : PhysicalKSBoxPointwiseData
      ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm) t0 M A F0 W)
    (hA : 1≤A) (hF0 : 0≤F0) (hh : 0<h) (hr : h≤physicalKSAnalyticAxisRadius M A) :
    SO2PolynomialSeriesInput
      (physicalKSAxisPlanePolynomialA ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm) t0)
      (fun z => physicalKSAnalyticDescentA
        ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm) t0 (physicalKSComplexAxisMap z))
      (16*physicalKSPointwiseAmplitude M A F0 W) h ∧
    SO2PolynomialSeriesInput
      (physicalKSAxisPlanePolynomialB ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm) t0)
      (fun z => physicalKSAnalyticDescentB
        ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm) t0 (physicalKSComplexAxisMap z))
      ((32*(7*physicalKSPointwiseRate M A)^2)*(16*physicalKSPointwiseAmplitude M A F0 W)) h :=
  physicalKSAxisPlaneSeries_data (nuclearKSPhysicalAxisPolynomial_data g i hdata hA hF0)
    (nuclearKSPhysicalAnalyticDescent_derivative_data g i hdata hA hF0) hA hF0 hh hr

theorem pairKSPhysicalAxisPlaneSeries_data
    (g : Configuration 2 → ℂ) {t0 : Position} {M A F0 W h : ℝ}
    (hdata : PhysicalKSBoxPointwiseData
      ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm) t0 M A F0 W)
    (hA : 1≤A) (hF0 : 0≤F0) (hh : 0<h) (hr : h≤physicalKSAnalyticAxisRadius M A) :
    SO2PolynomialSeriesInput
      (physicalKSAxisPlanePolynomialA ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm) t0)
      (fun z => physicalKSAnalyticDescentA
        ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm) t0 (physicalKSComplexAxisMap z))
      (16*physicalKSPointwiseAmplitude M A F0 W) h ∧
    SO2PolynomialSeriesInput
      (physicalKSAxisPlanePolynomialB ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm) t0)
      (fun z => physicalKSAnalyticDescentB
        ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm) t0 (physicalKSComplexAxisMap z))
      ((32*(7*physicalKSPointwiseRate M A)^2)*(16*physicalKSPointwiseAmplitude M A F0 W)) h :=
  physicalKSAxisPlaneSeries_data (pairKSPhysicalAxisPolynomial_data g hdata hA hF0)
    (pairKSPhysicalAnalyticDescent_derivative_data g hdata hA hF0) hA hF0 hh hr

end TheoremT.Continuum
