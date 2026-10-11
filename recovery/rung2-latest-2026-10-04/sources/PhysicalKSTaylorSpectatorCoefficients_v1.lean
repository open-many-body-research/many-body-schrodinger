import KSSpectatorCoefficientInvariance_v1
import PhysicalKSTaylorCircleInvariance_v1

/-! Genuine four-variable coefficients of the actual joint Taylor
polynomials, with exact derivative coefficients and inherited coefficient
budgets. The total order is j+degree(gamma), while j alone is the Y degree.
Circle invariance and balanced support are obtained from the actual
physical nuclear and pair chart Taylor identities. -/
set_option autoImplicit false
noncomputable section
namespace TheoremT.Continuum
open MvPolynomial WeakGrushin

def physicalKSTaylorSpectatorCoefficient (f : Space (Fin 3) → ℂ)
    (x : Space (Fin 3)) (j : ℕ) (γ : Fin 3 →₀ ℕ) : MvPolynomial (Fin 4) ℂ :=
  ksSpectatorCoefficientPolynomial (physicalKSTaylorPolynomial f x (j+γ.degree)) γ

theorem physicalKSTaylorSpectatorCoefficient_coeff
    (f : Space (Fin 3) → ℂ) (x : Space (Fin 3)) (j : ℕ) (γ : Fin 3 →₀ ℕ)
    (α : Fin 4 →₀ ℕ) :
    (physicalKSTaylorSpectatorCoefficient f x j γ).coeff α =
      (physicalKSTaylorPolynomial f x (j+γ.degree)).coeff (Finsupp.sumElim α γ) :=
  ksSpectatorCoefficientPolynomial_coeff _ γ α

theorem physicalKSTaylorSpectatorCoefficient_homogeneous
    (f : Space (Fin 3) → ℂ) (x : Space (Fin 3)) (j : ℕ) (γ : Fin 3 →₀ ℕ) :
    (physicalKSTaylorSpectatorCoefficient f x j γ).IsHomogeneous j := by
  simpa only [physicalKSTaylorSpectatorCoefficient,Nat.add_sub_cancel] using
    ksSpectatorCoefficientPolynomial_homogeneous
      (physicalKSTaylorPolynomial_homogeneous f x (j+γ.degree)) γ

theorem physicalKSTaylorSpectatorCoefficient_coefficientL1
    {f : Space (Fin 3) → ℂ} {t0 : Position} {M A F0 W : ℝ}
    (hdata : PhysicalKSBoxPointwiseData f t0 M A F0 W)
    (hA : 1≤A) (hF0 : 0≤F0) {x : Space (Fin 3)}
    (hx : x ∈ rectangularOpenBox (0,t0) (1/512) (1/512))
    (j : ℕ) (γ : Fin 3 →₀ ℕ) :
    polynomialCoeffL1 (physicalKSTaylorSpectatorCoefficient f x j γ) ≤
      physicalKSPointwiseAmplitude M A F0 W *
        (7*physicalKSPointwiseRate M A)^(j+γ.degree) :=
  (polynomialCoeffL1_ksSpectatorCoefficientPolynomial _ γ).trans
    (physicalKSTaylorPolynomial_coefficientL1 hdata hA hF0 hx (j+γ.degree))

theorem nuclearKSPhysicalTaylorSpectatorCoefficient_circle_invariant
    (g : Configuration 2 → ℂ) (i : Fin 2) {t0 : Position} {M A F0 W : ℝ}
    (hdata : PhysicalKSBoxPointwiseData
      ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm) t0 M A F0 W)
    (hA : 1≤A) (hF0 : 0≤F0) {a b : ℝ} (h : a^2+b^2=1)
    (j : ℕ) (γ : Fin 3 →₀ ℕ) (y : KSSpace) :
    eval (fun k => (ksCircleAction a b y k : ℂ))
        (physicalKSTaylorSpectatorCoefficient
          ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm) (0,t0) j γ) =
      eval (fun k => (y k : ℂ))
        (physicalKSTaylorSpectatorCoefficient
          ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm) (0,t0) j γ) := by
  apply ksSpectatorCoefficientPolynomial_circle_invariant
  intro q
  exact nuclearKSPhysicalTaylorPolynomial_circle_invariant g i hdata hA hF0 h (j+γ.degree) q

theorem pairKSPhysicalTaylorSpectatorCoefficient_circle_invariant
    (g : Configuration 2 → ℂ) {t0 : Position} {M A F0 W : ℝ}
    (hdata : PhysicalKSBoxPointwiseData
      ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm) t0 M A F0 W)
    (hA : 1≤A) (hF0 : 0≤F0) {a b : ℝ} (h : a^2+b^2=1)
    (j : ℕ) (γ : Fin 3 →₀ ℕ) (y : KSSpace) :
    eval (fun k => (ksCircleAction a b y k : ℂ))
        (physicalKSTaylorSpectatorCoefficient
          ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm) (0,t0) j γ) =
      eval (fun k => (y k : ℂ))
        (physicalKSTaylorSpectatorCoefficient
          ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm) (0,t0) j γ) := by
  apply ksSpectatorCoefficientPolynomial_circle_invariant
  intro q
  exact pairKSPhysicalTaylorPolynomial_circle_invariant g hdata hA hF0 h (j+γ.degree) q

theorem nuclearKSPhysicalTaylorSpectatorCoefficient_balanced_support
    (g : Configuration 2 → ℂ) (i : Fin 2) {t0 : Position} {M A F0 W : ℝ}
    (hdata : PhysicalKSBoxPointwiseData
      ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm) t0 M A F0 W)
    (hA : 1≤A) (hF0 : 0≤F0) (j : ℕ) (γ : Fin 3 →₀ ℕ) :
    ∀ d ∈ (ksRealPolynomialToSpinor (physicalKSTaylorSpectatorCoefficient
        ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm) (0,t0) j γ)).support,
      d 0+d 1=d 2+d 3 := by
  apply ksRealPolynomialToSpinor_balanced_support
  intro a b h y
  exact nuclearKSPhysicalTaylorSpectatorCoefficient_circle_invariant g i hdata hA hF0 h j γ y

theorem pairKSPhysicalTaylorSpectatorCoefficient_balanced_support
    (g : Configuration 2 → ℂ) {t0 : Position} {M A F0 W : ℝ}
    (hdata : PhysicalKSBoxPointwiseData
      ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm) t0 M A F0 W)
    (hA : 1≤A) (hF0 : 0≤F0) (j : ℕ) (γ : Fin 3 →₀ ℕ) :
    ∀ d ∈ (ksRealPolynomialToSpinor (physicalKSTaylorSpectatorCoefficient
        ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm) (0,t0) j γ)).support,
      d 0+d 1=d 2+d 3 := by
  apply ksRealPolynomialToSpinor_balanced_support
  intro a b h y
  exact pairKSPhysicalTaylorSpectatorCoefficient_circle_invariant g hdata hA hF0 h j γ y

end TheoremT.Continuum
