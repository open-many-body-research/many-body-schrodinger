import PhysicalKSTaylorSpectatorCoefficients_v1
import KSBalancedOddPolynomial_v1

/-! The actual nuclear and pair Taylor coefficient polynomials vanish at
odd Y degree. Spectator exponents remain arbitrary, so this does not assert
vanishing at odd total degree of the original seven-variable polynomial. -/
set_option autoImplicit false
noncomputable section
namespace TheoremT.Continuum
open MvPolynomial WeakGrushin

theorem nuclearKSPhysicalTaylorSpectatorCoefficient_odd_eq_zero
    (g : Configuration 2 → ℂ) (i : Fin 2) {t0 : Position} {M A F0 W : ℝ}
    (hdata : PhysicalKSBoxPointwiseData
      ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm) t0 M A F0 W)
    (hA : 1≤A) (hF0 : 0≤F0) (m : ℕ) (γ : Fin 3 →₀ ℕ) :
    physicalKSTaylorSpectatorCoefficient
      ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm)
        (0,t0) (2*m+1) γ = 0 :=
  ksRealPolynomial_odd_eq_zero_of_balanced
    (physicalKSTaylorSpectatorCoefficient_homogeneous _ _ _ _)
    (nuclearKSPhysicalTaylorSpectatorCoefficient_balanced_support
      g i hdata hA hF0 (2*m+1) γ)

theorem pairKSPhysicalTaylorSpectatorCoefficient_odd_eq_zero
    (g : Configuration 2 → ℂ) {t0 : Position} {M A F0 W : ℝ}
    (hdata : PhysicalKSBoxPointwiseData
      ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm) t0 M A F0 W)
    (hA : 1≤A) (hF0 : 0≤F0) (m : ℕ) (γ : Fin 3 →₀ ℕ) :
    physicalKSTaylorSpectatorCoefficient
      ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm)
        (0,t0) (2*m+1) γ = 0 :=
  ksRealPolynomial_odd_eq_zero_of_balanced
    (physicalKSTaylorSpectatorCoefficient_homogeneous _ _ _ _)
    (pairKSPhysicalTaylorSpectatorCoefficient_balanced_support
      g hdata hA hF0 (2*m+1) γ)

end TheoremT.Continuum
