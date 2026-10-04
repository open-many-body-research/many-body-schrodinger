import PhysicalKSAxisPlaneSeriesInvariance_v1

/-! Nuclear and pair collision plane-polynomial symmetry from actual
pointwise KS data and actual rotation invariance of the physical input.
The input function is not assumed to be an eigenfunction here. -/
noncomputable section
set_option autoImplicit false
namespace TheoremT.Continuum
open WeakGrushin

theorem nuclearKSPhysicalAxisPlanePolynomial_balanced_support
    (g : Configuration 2 → ℂ) (i : Fin 2) {c M A F0 W : ℝ}
    (hdata : PhysicalKSBoxPointwiseData
      ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm)
      (WithLp.toLp 2 ![0,0,c]) M A F0 W)
    (hA : 1≤A) (hF0 : 0≤F0)
    (hg : ∀ Q : Position ≃ₗᵢ[ℝ] Position, ∀ x, g (configurationRotation 2 Q x)=g x) :
    (∀ j γ d, d ∈ (so2PolynomialToBalanced
      (physicalKSAxisPlanePolynomialA
        ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm)
        (WithLp.toLp 2 ![0,0,c]) j γ)).support → d 0=d 1) ∧
    (∀ j γ d, d ∈ (so2PolynomialToBalanced
      (physicalKSAxisPlanePolynomialB
        ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm)
        (WithLp.toLp 2 ![0,0,c]) j γ)).support → d 0=d 1) :=
  physicalKSAxisPlanePolynomial_balanced_support
    (nuclearKSPhysicalAxisPolynomial_data g i hdata hA hF0)
    (nuclearKSPhysicalAnalyticDescent_invariant_derivative_data g i hdata hA hF0 hg) hA hF0

theorem pairKSPhysicalAxisPlanePolynomial_balanced_support
    (g : Configuration 2 → ℂ) {c M A F0 W : ℝ}
    (hdata : PhysicalKSBoxPointwiseData
      ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm)
      (WithLp.toLp 2 ![0,0,c]) M A F0 W)
    (hA : 1≤A) (hF0 : 0≤F0)
    (hg : ∀ Q : Position ≃ₗᵢ[ℝ] Position, ∀ x, g (configurationRotation 2 Q x)=g x) :
    (∀ j γ d, d ∈ (so2PolynomialToBalanced
      (physicalKSAxisPlanePolynomialA
        ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm)
        (WithLp.toLp 2 ![0,0,c]) j γ)).support → d 0=d 1) ∧
    (∀ j γ d, d ∈ (so2PolynomialToBalanced
      (physicalKSAxisPlanePolynomialB
        ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm)
        (WithLp.toLp 2 ![0,0,c]) j γ)).support → d 0=d 1) :=
  physicalKSAxisPlanePolynomial_balanced_support
    (pairKSPhysicalAxisPolynomial_data g hdata hA hF0)
    (pairKSPhysicalAnalyticDescent_invariant_derivative_data g hdata hA hF0 hg) hA hF0

end TheoremT.Continuum
