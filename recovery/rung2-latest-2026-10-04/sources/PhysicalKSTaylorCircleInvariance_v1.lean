import PhysicalKSTaylorCoordinatePolynomials_v1
import PowerSeriesFixedPointInvariance_v1
import KSPhysicalCircleInvariance_v1

/-! Circle invariance of the actual joint Taylor polynomials at the physical
KS collision fiber. Invariance is deduced from the actual pullback identity
and convergent derivative series, not imposed on polynomial coefficients. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
open scoped Topology NNReal ENNReal
namespace TheoremT.Continuum
open MvPolynomial WeakGrushin

theorem physicalKSTaylorPolynomial_invariant_at_center
    {f : Space (Fin 3) → ℂ} {t0 : Position} {M A F0 W : ℝ}
    (hdata : PhysicalKSBoxPointwiseData f t0 M A F0 W)
    (hA : 1≤A) (hF0 : 0≤F0) (L : Space (Fin 3) →L[ℝ] Space (Fin 3))
    (hfixed : L (0,t0)=(0,t0))
    (hInv : (f ∘ L) =ᶠ[𝓝 (0,t0)] f) (k : ℕ) (y : Space (Fin 3)) :
    eval (fun j => (productCoordinateComponent (L y) j : ℂ))
        (physicalKSTaylorPolynomial f (0,t0) k) =
      eval (fun j => (productCoordinateComponent y j : ℂ))
        (physicalKSTaylorPolynomial f (0,t0) k) := by
  obtain ⟨r,hr,he,hs⟩ := physicalKSBoxPointwiseData_common_radius hdata hA hF0
  have hcenter : (0,t0) ∈ rectangularClosedBox (0,t0) (1/1024) (1/1024) := by
    intro j
    cases j <;> simp [boxHalfWidth]
  have hf := (hs (0,t0) hcenter).hasFPowerSeriesAt
  unfold physicalKSTaylorPolynomial
  rw [realTaylorCoordinatePolynomial_eval productCoordinateDirection productCoordinateComponent
    productCoordinateComponent_reconstruct,
    realTaylorCoordinatePolynomial_eval productCoordinateDirection productCoordinateComponent
      productCoordinateComponent_reconstruct]
  exact powerSeries_diagonal_invariant_at_fixed_point hf L hfixed hInv k y

theorem nuclearKSPhysicalTaylorPolynomial_circle_invariant
    (g : Configuration 2 → ℂ) (i : Fin 2) {t0 : Position} {M A F0 W : ℝ}
    (hdata : PhysicalKSBoxPointwiseData
      ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm) t0 M A F0 W)
    (hA : 1≤A) (hF0 : 0≤F0) {a b : ℝ} (h : a^2+b^2=1)
    (k : ℕ) (y : Space (Fin 3)) :
    eval (fun j => (productCoordinateComponent (ksCircleProductCLM a b y) j : ℂ))
        (physicalKSTaylorPolynomial
          ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm) (0,t0) k) =
      eval (fun j => (productCoordinateComponent y j : ℂ))
        (physicalKSTaylorPolynomial
          ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm) (0,t0) k) := by
  apply physicalKSTaylorPolynomial_invariant_at_center hdata hA hF0
    (ksCircleProductCLM a b) (ksCircleProductCLM_fixed a b t0)
  exact Filter.Eventually.of_forall (nuclearKSPhysicalPullback_circle_invariant g i h)

theorem pairKSPhysicalTaylorPolynomial_circle_invariant
    (g : Configuration 2 → ℂ) {t0 : Position} {M A F0 W : ℝ}
    (hdata : PhysicalKSBoxPointwiseData
      ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm) t0 M A F0 W)
    (hA : 1≤A) (hF0 : 0≤F0) {a b : ℝ} (h : a^2+b^2=1)
    (k : ℕ) (y : Space (Fin 3)) :
    eval (fun j => (productCoordinateComponent (ksCircleProductCLM a b y) j : ℂ))
        (physicalKSTaylorPolynomial
          ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm) (0,t0) k) =
      eval (fun j => (productCoordinateComponent y j : ℂ))
        (physicalKSTaylorPolynomial
          ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm) (0,t0) k) := by
  apply physicalKSTaylorPolynomial_invariant_at_center hdata hA hF0
    (ksCircleProductCLM a b) (ksCircleProductCLM_fixed a b t0)
  exact Filter.Eventually.of_forall (pairKSPhysicalPullback_circle_invariant g h)

end TheoremT.Continuum
