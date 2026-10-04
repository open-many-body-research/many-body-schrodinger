import RealTaylorCoordinatePolynomial_v1
import PhysicalKSBoxAnalyticRadius_v1

/-! Actual seven-coordinate Taylor polynomials of the physical KS base.
These are joint Y/spectator polynomials, without assuming complexified
Taylor coefficients or any invariant-polynomial decomposition. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators ENNReal NNReal
namespace TheoremT.Continuum
open MvPolynomial WeakGrushin

def physicalKSTaylorPolynomial (f : Space (Fin 3) → ℂ) (x : Space (Fin 3)) (k : ℕ) :
    MvPolynomial (Fin 4 ⊕ Fin 3) ℂ :=
  realTaylorCoordinatePolynomial productCoordinateDirection f x k

theorem physicalKSTaylorPolynomial_homogeneous
    (f : Space (Fin 3) → ℂ) (x : Space (Fin 3)) (k : ℕ) :
    (physicalKSTaylorPolynomial f x k).IsHomogeneous k :=
  realTaylorCoordinatePolynomial_homogeneous _ f x k

theorem physicalKSTaylorPolynomial_coefficientL1
    {f : Space (Fin 3) → ℂ} {t0 : Position} {M A F0 W : ℝ}
    (hdata : PhysicalKSBoxPointwiseData f t0 M A F0 W)
    (hA : 1 ≤ A) (hF0 : 0 ≤ F0) {x : Space (Fin 3)}
    (hx : x ∈ rectangularOpenBox (0,t0) (1/512) (1/512)) (k : ℕ) :
    polynomialCoeffL1 (physicalKSTaylorPolynomial f x k) ≤
      physicalKSPointwiseAmplitude M A F0 W * (7*physicalKSPointwiseRate M A)^k := by
  have hbound (w : Fin k → Fin 4 ⊕ Fin 3) :
      ‖iteratedFDeriv ℝ k f x (fun i => productCoordinateDirection (w i))‖ ≤
        physicalKSPointwiseAmplitude M A F0 W *
          (physicalKSPointwiseRate M A)^k * (k.factorial : ℝ) := by
    rw [← complexDirectionalWordDeriv_ofFn_eq_iteratedFDeriv productCoordinateDirection
      (rectangularOpenBox_isOpen (0,t0) _ _) hdata.1 w hx]
    simpa only [List.length_ofFn] using hdata.2.2 (List.ofFn w) x hx
  have h := polynomialCoeffL1_realTaylorCoordinatePolynomial productCoordinateDirection f x k
    (physicalKSPointwiseAmplitude_nonneg hA hF0) (physicalKSPointwiseRate_pos hA).le hbound
  simpa [physicalKSTaylorPolynomial] using h

theorem physicalKSTaylorPolynomial_common_radius
    {f : Space (Fin 3) → ℂ} {t0 : Position} {M A F0 W : ℝ}
    (hdata : PhysicalKSBoxPointwiseData f t0 M A F0 W)
    (hA : 1 ≤ A) (hF0 : 0 ≤ F0) :
    ∃ r : ℝ≥0, 0 < r ∧ (r : ℝ) = min (1/1024) (7*physicalKSPointwiseRate M A)⁻¹ ∧
      ∀ x ∈ rectangularClosedBox (0,t0) (1/1024) (1/1024),
        ∀ y ∈ Metric.eball (0 : Space (Fin 3)) (r : ℝ≥0∞),
          HasSum (fun k => eval (fun j => (productCoordinateComponent y j : ℂ))
            (physicalKSTaylorPolynomial f x k)) (f (x+y)) := by
  obtain ⟨r,hr,he,hs⟩ := physicalKSBoxPointwiseData_common_radius hdata hA hF0
  refine ⟨r,hr,he,?_⟩
  intro x hx y hy
  exact realTaylorCoordinatePolynomial_hasSum productCoordinateDirection
    productCoordinateComponent productCoordinateComponent_reconstruct f x (hs x hx) hy

end TheoremT.Continuum
