import PhysicalKSTaylorCoordinatePolynomials_v1
import HomogeneousPolynomialSeriesAnalytic_v1
import HomogeneousPolynomialGeometricSeries_v1

/-! An actual complex extension of the physical KS Taylor series, built as
the literal sum of the proved coordinate polynomials. The complex domain
uses the coordinate sup norm; agreement with the actual real physical base
uses the previously proved real product-norm convergence ball. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators NNReal ENNReal
namespace TheoremT.Continuum
open MvPolynomial WeakGrushin

def physicalKSComplexTaylorExtension (f : Space (Fin 3) → ℂ) (x : Space (Fin 3))
    (z : Fin 4 ⊕ Fin 3 → ℂ) : ℂ :=
  ∑' k, eval z (physicalKSTaylorPolynomial f x k)

theorem physicalKSComplexTaylorExtension_analytic
    {f : Space (Fin 3) → ℂ} {t0 : Position} {M A F0 W : ℝ}
    (hdata : PhysicalKSBoxPointwiseData f t0 M A F0 W)
    (hA : 1≤A) (hF0 : 0≤F0) {x : Space (Fin 3)}
    (hx : x ∈ rectangularOpenBox (0,t0) (1/512) (1/512)) :
    AnalyticOnNhd ℂ (physicalKSComplexTaylorExtension f x)
      {z : Fin 4 ⊕ Fin 3 → ℂ | (7*physicalKSPointwiseRate M A)*‖z‖<1} := by
  exact homogeneous_polynomial_series_analyticOnNhd _
    (physicalKSTaylorPolynomial_homogeneous f x)
    (physicalKSPointwiseAmplitude_nonneg hA hF0)
    (mul_nonneg (by norm_num) (physicalKSPointwiseRate_pos hA).le)
    (physicalKSTaylorPolynomial_coefficientL1 hdata hA hF0 hx)

theorem physicalKSComplexTaylorExtension_norm_bound
    {f : Space (Fin 3) → ℂ} {t0 : Position} {M A F0 W : ℝ}
    (hdata : PhysicalKSBoxPointwiseData f t0 M A F0 W)
    (hA : 1≤A) (hF0 : 0≤F0) {x : Space (Fin 3)}
    (hx : x ∈ rectangularOpenBox (0,t0) (1/512) (1/512))
    {r : ℝ} (hr : 0≤r) (hsmall : (7*physicalKSPointwiseRate M A)*r<1)
    (z : Fin 4 ⊕ Fin 3 → ℂ) (hz : z ∈ complexClosedPolydisc (Fin 4 ⊕ Fin 3) r) :
    ‖physicalKSComplexTaylorExtension f x z‖ ≤
      physicalKSPointwiseAmplitude M A F0 W/(1-(7*physicalKSPointwiseRate M A)*r) := by
  exact homogeneous_polynomial_series_norm_tsum_le _
    (physicalKSTaylorPolynomial_homogeneous f x)
    (mul_nonneg (by norm_num) (physicalKSPointwiseRate_pos hA).le) hr hsmall
    (physicalKSTaylorPolynomial_coefficientL1 hdata hA hF0 hx) z hz

theorem physicalKSComplexTaylorExtension_agrees_on_real_ball
    {f : Space (Fin 3) → ℂ} {t0 : Position} {M A F0 W : ℝ}
    (hdata : PhysicalKSBoxPointwiseData f t0 M A F0 W)
    (hA : 1≤A) (hF0 : 0≤F0) :
    ∃ r : ℝ≥0, 0<r ∧ (r : ℝ)=min (1/1024) (7*physicalKSPointwiseRate M A)⁻¹ ∧
      ∀ x ∈ rectangularClosedBox (0,t0) (1/1024) (1/1024),
        ∀ y ∈ Metric.eball (0 : Space (Fin 3)) (r : ℝ≥0∞),
          physicalKSComplexTaylorExtension f x
            (fun j => (productCoordinateComponent y j : ℂ)) = f (x+y) := by
  obtain ⟨r,hr,he,hs⟩ := physicalKSTaylorPolynomial_common_radius hdata hA hF0
  refine ⟨r,hr,he,?_⟩
  intro x hx y hy
  exact (hs x hx y hy).tsum_eq

end TheoremT.Continuum
