import SO2PolynomialSeriesAnalyticDescent_v1
import PhysicalKSAxisPlaneSeriesInvariance_v1

/-! Actual physical KS axis descent through w=x²+y². The functions are
the prescribed sums of the actual Cartesian axial coefficients, and are
jointly holomorphic with the same proved bounds on the full descended
polydisc. The original physical function identity uses the domain
intersection stated by SO2AnalyticDescentData. -/
noncomputable section
set_option autoImplicit false
namespace TheoremT.Continuum
open WeakGrushin

def physicalKSAxisDescendedA (f : Space (Fin 3) → ℂ) (t0 : Position) :=
  scalarSpectatorSum (so2DescendedCoefficient (physicalKSAxisPlanePolynomialA f t0))

def physicalKSAxisDescendedB (f : Space (Fin 3) → ℂ) (t0 : Position) :=
  scalarSpectatorSum (so2DescendedCoefficient (physicalKSAxisPlanePolynomialB f t0))

def PhysicalKSAxisAnalyticDescentData
    (f : Space (Fin 3) → ℂ) (t0 : Position) (M A F0 W h : ℝ) : Prop :=
  SO2AnalyticDescentData
    (fun z => physicalKSAnalyticDescentA f t0 (physicalKSComplexAxisMap z))
    (physicalKSAxisDescendedA f t0) (16*physicalKSPointwiseAmplitude M A F0 W) h ∧
  SO2AnalyticDescentData
    (fun z => physicalKSAnalyticDescentB f t0 (physicalKSComplexAxisMap z))
    (physicalKSAxisDescendedB f t0)
    ((32*(7*physicalKSPointwiseRate M A)^2)*(16*physicalKSPointwiseAmplitude M A F0 W)) h

theorem physicalKSAxisAnalyticDescent_data
    {f : Space (Fin 3) → ℂ} {v : Position → Position → ℂ} {c M A F0 W h : ℝ}
    (hq : PhysicalKSAxisPolynomialData f (WithLp.toLp 2 ![0,0,c]) M A F0 W)
    (hdata : PhysicalKSBoxInvariantAnalyticDescentDerivativeData
      f v (WithLp.toLp 2 ![0,0,c]) M A F0 W)
    (hA : 1≤A) (hF0 : 0≤F0) (hh : 0<h) (hr : h≤physicalKSAnalyticAxisRadius M A) :
    PhysicalKSAxisAnalyticDescentData f (WithLp.toLp 2 ![0,0,c]) M A F0 W h := by
  have hi := physicalKSAxisPlaneSeries_data hq hdata.1 hA hF0 hh hr
  have hb := physicalKSAxisPlanePolynomial_balanced_support hq hdata hA hF0
  have hp := physicalKSPointwiseAmplitude_nonneg (M := M) (W := W) hA hF0
  exact ⟨so2PolynomialSeriesInput_analytic_descent _ _ hi.1 hb.1 (by positivity) hh,
    so2PolynomialSeriesInput_analytic_descent _ _ hi.2 hb.2 (by positivity) hh⟩

theorem nuclearKSPhysicalAxisAnalyticDescent_data
    (g : Configuration 2 → ℂ) (i : Fin 2) {c M A F0 W h : ℝ}
    (hdata : PhysicalKSBoxPointwiseData
      ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm)
      (WithLp.toLp 2 ![0,0,c]) M A F0 W)
    (hA : 1≤A) (hF0 : 0≤F0)
    (hg : ∀ Q : Position ≃ₗᵢ[ℝ] Position, ∀ x, g (configurationRotation 2 Q x) = g x)
    (hh : 0<h) (hr : h≤physicalKSAnalyticAxisRadius M A) :
    PhysicalKSAxisAnalyticDescentData
      ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm)
      (WithLp.toLp 2 ![0,0,c]) M A F0 W h :=
  physicalKSAxisAnalyticDescent_data (nuclearKSPhysicalAxisPolynomial_data g i hdata hA hF0)
    (nuclearKSPhysicalAnalyticDescent_invariant_derivative_data g i hdata hA hF0 hg)
    hA hF0 hh hr

theorem pairKSPhysicalAxisAnalyticDescent_data
    (g : Configuration 2 → ℂ) {c M A F0 W h : ℝ}
    (hdata : PhysicalKSBoxPointwiseData
      ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm)
      (WithLp.toLp 2 ![0,0,c]) M A F0 W)
    (hA : 1≤A) (hF0 : 0≤F0)
    (hg : ∀ Q : Position ≃ₗᵢ[ℝ] Position, ∀ x, g (configurationRotation 2 Q x) = g x)
    (hh : 0<h) (hr : h≤physicalKSAnalyticAxisRadius M A) :
    PhysicalKSAxisAnalyticDescentData
      ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm)
      (WithLp.toLp 2 ![0,0,c]) M A F0 W h :=
  physicalKSAxisAnalyticDescent_data (pairKSPhysicalAxisPolynomial_data g hdata hA hF0)
    (pairKSPhysicalAnalyticDescent_invariant_derivative_data g hdata hA hF0 hg)
    hA hF0 hh hr

end TheoremT.Continuum
