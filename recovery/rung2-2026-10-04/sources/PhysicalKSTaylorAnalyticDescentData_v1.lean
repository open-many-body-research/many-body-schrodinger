import PhysicalKSTaylorSpectatorSeries_v1
import KSRealSpectatorSeriesData_v1

/-! The analytic A and B series are defined from the actual physical Taylor
coefficients. Nuclear and pair chart wrappers prove their input balance from
the actual chart symmetry. Identification with the physical function is
handled separately through the original convergent Taylor series. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum
open MvPolynomial WeakGrushin

def physicalKSTaylorEvenSpectatorFamily (f : Space (Fin 3) → ℂ)
    (x : Space (Fin 3)) (m : ℕ) (γ : Fin 3 → ℕ) : MvPolynomial (Fin 4) ℂ :=
  physicalKSTaylorSpectatorFamily f x (2*m) γ

def physicalKSAnalyticDescentA (f : Space (Fin 3) → ℂ) (t0 : Position)
    (z : Fin 3 ⊕ Fin 3 → ℂ) : ℂ :=
  homogeneousSpectatorSum (ksRealSpectatorFamilyA (physicalKSTaylorEvenSpectatorFamily f (0,t0))) z

def physicalKSAnalyticDescentB (f : Space (Fin 3) → ℂ) (t0 : Position)
    (z : Fin 3 ⊕ Fin 3 → ℂ) : ℂ :=
  homogeneousSpectatorSum (ksRealSpectatorFamilyB (physicalKSTaylorEvenSpectatorFamily f (0,t0))) z

theorem physicalKSTaylorEvenSpectatorFamily_homogeneous
    (f : Space (Fin 3) → ℂ) (x : Space (Fin 3)) (m : ℕ) (γ : Fin 3 → ℕ) :
    (physicalKSTaylorEvenSpectatorFamily f x m γ).IsHomogeneous (2*m) :=
  physicalKSTaylorSpectatorFamily_homogeneous f x (2*m) γ

theorem physicalKSTaylorEvenSpectatorFamily_coeff_bound
    {f : Space (Fin 3) → ℂ} {t0 : Position} {M A F0 W : ℝ}
    (hdata : PhysicalKSBoxPointwiseData f t0 M A F0 W)
    (hA : 1≤A) (hF0 : 0≤F0) (m : ℕ) (γ : Fin 3 → ℕ) (e : Fin 4 →₀ ℕ) :
    ‖(physicalKSTaylorEvenSpectatorFamily f (0,t0) m γ).coeff e‖ ≤
      physicalKSPointwiseAmplitude M A F0 W *
        (7*physicalKSPointwiseRate M A)^(2*m) *
        (7*physicalKSPointwiseRate M A)^(∑ i : Fin 3, γ i) := by
  apply (polynomialCoeffL1_coefficient_bound _ e).trans
  apply physicalKSTaylorSpectatorFamily_coefficientL1 hdata hA hF0
  intro i
  cases i <;> norm_num [boxHalfWidth]

theorem physicalKSAnalyticDescent_analytic_of_balanced
    {f : Space (Fin 3) → ℂ} {t0 : Position} {M A F0 W : ℝ}
    (hdata : PhysicalKSBoxPointwiseData f t0 M A F0 W)
    (hA : 1≤A) (hF0 : 0≤F0)
    (hbal : ∀ m γ e, e ∈ (ksRealPolynomialToSpinor
      (physicalKSTaylorEvenSpectatorFamily f (0,t0) m γ)).support → e 0+e 1=e 2+e 3) :
    AnalyticOnNhd ℂ (physicalKSAnalyticDescentA f t0)
      {z : Fin 3 ⊕ Fin 3 → ℂ |
        (32*(7*physicalKSPointwiseRate M A)^2)*‖fun i : Fin 3 => z (.inl i)‖ < 1 ∧
        (7*physicalKSPointwiseRate M A)*‖fun i : Fin 3 => z (.inr i)‖ < 1} ∧
    AnalyticOnNhd ℂ (physicalKSAnalyticDescentB f t0)
      {z : Fin 3 ⊕ Fin 3 → ℂ |
        (32*(7*physicalKSPointwiseRate M A)^2)*‖fun i : Fin 3 => z (.inl i)‖ < 1 ∧
        (7*physicalKSPointwiseRate M A)*‖fun i : Fin 3 => z (.inr i)‖ < 1} := by
  have hS : 0 ≤ 7*physicalKSPointwiseRate M A :=
    mul_nonneg (by norm_num) (physicalKSPointwiseRate_pos hA).le
  exact ks_real_spectator_series_analytic _
    (physicalKSTaylorEvenSpectatorFamily_homogeneous f (0,t0)) hbal
    (physicalKSPointwiseAmplitude_nonneg hA hF0) hS hS
    (fun m γ e _ => physicalKSTaylorEvenSpectatorFamily_coeff_bound hdata hA hF0 m γ e)

theorem nuclearKSPhysicalAnalyticDescent_analytic
    (g : Configuration 2 → ℂ) (i : Fin 2) {t0 : Position} {M A F0 W : ℝ}
    (hdata : PhysicalKSBoxPointwiseData
      ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm) t0 M A F0 W)
    (hA : 1≤A) (hF0 : 0≤F0) :
    AnalyticOnNhd ℂ (physicalKSAnalyticDescentA
      ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm) t0)
      {z : Fin 3 ⊕ Fin 3 → ℂ |
        (32*(7*physicalKSPointwiseRate M A)^2)*‖fun j : Fin 3 => z (.inl j)‖ < 1 ∧
        (7*physicalKSPointwiseRate M A)*‖fun j : Fin 3 => z (.inr j)‖ < 1} ∧
    AnalyticOnNhd ℂ (physicalKSAnalyticDescentB
      ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm) t0)
      {z : Fin 3 ⊕ Fin 3 → ℂ |
        (32*(7*physicalKSPointwiseRate M A)^2)*‖fun j : Fin 3 => z (.inl j)‖ < 1 ∧
        (7*physicalKSPointwiseRate M A)*‖fun j : Fin 3 => z (.inr j)‖ < 1} := by
  apply physicalKSAnalyticDescent_analytic_of_balanced hdata hA hF0
  intro m γ e he
  exact nuclearKSPhysicalTaylorSpectatorCoefficient_balanced_support g i hdata hA hF0
    (2*m) (Finsupp.equivFunOnFinite.symm γ) e he

theorem pairKSPhysicalAnalyticDescent_analytic
    (g : Configuration 2 → ℂ) {t0 : Position} {M A F0 W : ℝ}
    (hdata : PhysicalKSBoxPointwiseData
      ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm) t0 M A F0 W)
    (hA : 1≤A) (hF0 : 0≤F0) :
    AnalyticOnNhd ℂ (physicalKSAnalyticDescentA
      ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm) t0)
      {z : Fin 3 ⊕ Fin 3 → ℂ |
        (32*(7*physicalKSPointwiseRate M A)^2)*‖fun j : Fin 3 => z (.inl j)‖ < 1 ∧
        (7*physicalKSPointwiseRate M A)*‖fun j : Fin 3 => z (.inr j)‖ < 1} ∧
    AnalyticOnNhd ℂ (physicalKSAnalyticDescentB
      ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm) t0)
      {z : Fin 3 ⊕ Fin 3 → ℂ |
        (32*(7*physicalKSPointwiseRate M A)^2)*‖fun j : Fin 3 => z (.inl j)‖ < 1 ∧
        (7*physicalKSPointwiseRate M A)*‖fun j : Fin 3 => z (.inr j)‖ < 1} := by
  apply physicalKSAnalyticDescent_analytic_of_balanced hdata hA hF0
  intro m γ e he
  exact pairKSPhysicalTaylorSpectatorCoefficient_balanced_support g hdata hA hF0
    (2*m) (Finsupp.equivFunOnFinite.symm γ) e he

end TheoremT.Continuum
