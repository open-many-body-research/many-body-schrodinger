import PhysicalKSTaylorAnalyticDescentData_v1
import KSRealSpectatorSeriesDerivative_v1

/-! Quantitative mixed derivatives of the A and B functions constructed
from the actual physical Taylor pieces. Nuclear and pair chart balance
is discharged from the actual lift, rather than postulated. The corrected
dimension factor 24 and the quarter product polydisc are explicit.
Pointwise KS box data remains an input to these component theorems. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum
open WeakGrushin

def physicalKSDescentDerivativeBudget (M A F0 W : ℝ) (α β : Fin 3 → ℕ) : ℝ :=
  (16*physicalKSPointwiseAmplitude M A F0 W)*
    (24*(32*(7*physicalKSPointwiseRate M A)^2))^(∑ i, α i)*
    (24*(7*physicalKSPointwiseRate M A))^(∑ i, β i)*
    (∏ i, ((α i).factorial : ℝ))*(∏ i, ((β i).factorial : ℝ))

theorem physicalKSAnalyticDescent_mixed_derivative_of_balanced
    {f : Space (Fin 3) → ℂ} {t0 : Position} {M A F0 W : ℝ}
    (hdata : PhysicalKSBoxPointwiseData f t0 M A F0 W)
    (hA : 1 ≤ A) (hF0 : 0 ≤ F0)
    (hbal : ∀ m γ e, e ∈ (ksRealPolynomialToSpinor
      (physicalKSTaylorEvenSpectatorFamily f (0,t0) m γ)).support → e 0+e 1=e 2+e 3)
    (z : Fin 3 ⊕ Fin 3 → ℂ)
    (hX : (32*(7*physicalKSPointwiseRate M A)^2)*‖fun i : Fin 3 => z (.inl i)‖ ≤ 1/4)
    (hs : (7*physicalKSPointwiseRate M A)*‖fun i : Fin 3 => z (.inr i)‖ ≤ 1/4)
    (α β : Fin 3 → ℕ) :
    ‖complexMultiindexDeriv (physicalKSAnalyticDescentA f t0) (Sum.elim α β) z‖ ≤
      physicalKSDescentDerivativeBudget M A F0 W α β ∧
    ‖complexMultiindexDeriv (physicalKSAnalyticDescentB f t0) (Sum.elim α β) z‖ ≤
      (32*(7*physicalKSPointwiseRate M A)^2)*physicalKSDescentDerivativeBudget M A F0 W α β := by
  have hpos : 0 < 7*physicalKSPointwiseRate M A :=
    mul_pos (by norm_num) (physicalKSPointwiseRate_pos hA)
  have h := ks_real_spectator_series_mixed_factorial_bounds _
    (physicalKSTaylorEvenSpectatorFamily_homogeneous f (0,t0)) hbal
    (physicalKSPointwiseAmplitude_nonneg hA hF0) hpos hpos
    (fun m γ e _ => physicalKSTaylorEvenSpectatorFamily_coeff_bound hdata hA hF0 m γ e)
    z hX hs α β
  norm_num at h
  dsimp only [physicalKSAnalyticDescentA,physicalKSAnalyticDescentB,physicalKSDescentDerivativeBudget]
  constructor
  · convert h.1 using 1 <;> first | rfl | ring
  · convert h.2 using 1 <;> first | rfl | ring

theorem nuclearKSPhysicalAnalyticDescent_mixed_derivative
    (g : Configuration 2 → ℂ) (i : Fin 2) {t0 : Position} {M A F0 W : ℝ}
    (hdata : PhysicalKSBoxPointwiseData
      ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm) t0 M A F0 W)
    (hA : 1 ≤ A) (hF0 : 0 ≤ F0)
    (z : Fin 3 ⊕ Fin 3 → ℂ)
    (hX : (32*(7*physicalKSPointwiseRate M A)^2)*‖fun j : Fin 3 => z (.inl j)‖ ≤ 1/4)
    (hs : (7*physicalKSPointwiseRate M A)*‖fun j : Fin 3 => z (.inr j)‖ ≤ 1/4)
    (α β : Fin 3 → ℕ) :
    ‖complexMultiindexDeriv (physicalKSAnalyticDescentA
      ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm) t0) (Sum.elim α β) z‖ ≤
      physicalKSDescentDerivativeBudget M A F0 W α β ∧
    ‖complexMultiindexDeriv (physicalKSAnalyticDescentB
      ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm) t0) (Sum.elim α β) z‖ ≤
      (32*(7*physicalKSPointwiseRate M A)^2)*physicalKSDescentDerivativeBudget M A F0 W α β := by
  apply physicalKSAnalyticDescent_mixed_derivative_of_balanced hdata hA hF0 _ z hX hs α β
  intro m γ e he
  exact nuclearKSPhysicalTaylorSpectatorCoefficient_balanced_support g i hdata hA hF0
    (2*m) (Finsupp.equivFunOnFinite.symm γ) e he

theorem pairKSPhysicalAnalyticDescent_mixed_derivative
    (g : Configuration 2 → ℂ) {t0 : Position} {M A F0 W : ℝ}
    (hdata : PhysicalKSBoxPointwiseData
      ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm) t0 M A F0 W)
    (hA : 1 ≤ A) (hF0 : 0 ≤ F0)
    (z : Fin 3 ⊕ Fin 3 → ℂ)
    (hX : (32*(7*physicalKSPointwiseRate M A)^2)*‖fun j : Fin 3 => z (.inl j)‖ ≤ 1/4)
    (hs : (7*physicalKSPointwiseRate M A)*‖fun j : Fin 3 => z (.inr j)‖ ≤ 1/4)
    (α β : Fin 3 → ℕ) :
    ‖complexMultiindexDeriv (physicalKSAnalyticDescentA
      ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm) t0) (Sum.elim α β) z‖ ≤
      physicalKSDescentDerivativeBudget M A F0 W α β ∧
    ‖complexMultiindexDeriv (physicalKSAnalyticDescentB
      ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm) t0) (Sum.elim α β) z‖ ≤
      (32*(7*physicalKSPointwiseRate M A)^2)*physicalKSDescentDerivativeBudget M A F0 W α β := by
  apply physicalKSAnalyticDescent_mixed_derivative_of_balanced hdata hA hF0 _ z hX hs α β
  intro m γ e he
  exact pairKSPhysicalTaylorSpectatorCoefficient_balanced_support g hdata hA hF0
    (2*m) (Finsupp.equivFunOnFinite.symm γ) e he

end TheoremT.Continuum
