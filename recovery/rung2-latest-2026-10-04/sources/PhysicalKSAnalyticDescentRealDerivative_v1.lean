import PhysicalKSAnalyticDescentDerivative_v1
import HomogeneousSpectatorRealDerivative_v1

/-! Actual real mixed derivatives of the physical KS A/B coefficient
functions. Complex analyticity and the exact scalar-restriction identity
discharge the real differentiation bridge without a numerical factor. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum
open WeakGrushin

theorem physicalKSAnalyticDescent_real_mixed_derivative_of_balanced
    {f : Space (Fin 3) → ℂ} {t0 : Position} {M A F0 W : ℝ}
    (hdata : PhysicalKSBoxPointwiseData f t0 M A F0 W)
    (hA : 1 ≤ A) (hF0 : 0 ≤ F0)
    (hbal : ∀ m γ e, e ∈ (ksRealPolynomialToSpinor
      (physicalKSTaylorEvenSpectatorFamily f (0,t0) m γ)).support → e 0+e 1=e 2+e 3)
    (z : Fin 3 ⊕ Fin 3 → ℝ)
    (hX : (32*(7*physicalKSPointwiseRate M A)^2)*‖fun i : Fin 3 => z (.inl i)‖ ≤ 1/4)
    (hs : (7*physicalKSPointwiseRate M A)*‖fun i : Fin 3 => z (.inr i)‖ ≤ 1/4)
    (α β : Fin 3 → ℕ) :
    ‖realMultiindexDeriv
      (fun x : Fin 3 ⊕ Fin 3 → ℝ => physicalKSAnalyticDescentA f t0 (fun i => (x i : ℂ)))
      (Sum.elim α β) z‖ ≤ physicalKSDescentDerivativeBudget M A F0 W α β ∧
    ‖realMultiindexDeriv
      (fun x : Fin 3 ⊕ Fin 3 → ℝ => physicalKSAnalyticDescentB f t0 (fun i => (x i : ℂ)))
      (Sum.elim α β) z‖ ≤
      (32*(7*physicalKSPointwiseRate M A)^2)*physicalKSDescentDerivativeBudget M A F0 W α β := by
  have hXc : (32*(7*physicalKSPointwiseRate M A)^2)*‖fun i : Fin 3 => (z (.inl i) : ℂ)‖ ≤ 1/4 := by
    simpa only [finite_real_complexification_norm] using hX
  have hsc : (7*physicalKSPointwiseRate M A)*‖fun i : Fin 3 => (z (.inr i) : ℂ)‖ ≤ 1/4 := by
    simpa only [finite_real_complexification_norm] using hs
  have hana := physicalKSAnalyticDescent_analytic_of_balanced hdata hA hF0 hbal
  have hz : (fun i => (z i : ℂ)) ∈
      {v : Fin 3 ⊕ Fin 3 → ℂ |
        (32*(7*physicalKSPointwiseRate M A)^2)*‖fun i : Fin 3 => v (.inl i)‖ < 1 ∧
        (7*physicalKSPointwiseRate M A)*‖fun i : Fin 3 => v (.inr i)‖ < 1} :=
    ⟨by linarith,by linarith⟩
  rw [realMultiindexDeriv_restriction _ _ _ (hana.1 _ hz).contDiffAt,
    realMultiindexDeriv_restriction _ _ _ (hana.2 _ hz).contDiffAt]
  exact physicalKSAnalyticDescent_mixed_derivative_of_balanced hdata hA hF0 hbal _ hXc hsc α β

theorem nuclearKSPhysicalAnalyticDescent_real_mixed_derivative
    (g : Configuration 2 → ℂ) (i : Fin 2) {t0 : Position} {M A F0 W : ℝ}
    (hdata : PhysicalKSBoxPointwiseData
      ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm) t0 M A F0 W)
    (hA : 1 ≤ A) (hF0 : 0 ≤ F0)
    (z : Fin 3 ⊕ Fin 3 → ℝ)
    (hX : (32*(7*physicalKSPointwiseRate M A)^2)*‖fun j : Fin 3 => z (.inl j)‖ ≤ 1/4)
    (hs : (7*physicalKSPointwiseRate M A)*‖fun j : Fin 3 => z (.inr j)‖ ≤ 1/4)
    (α β : Fin 3 → ℕ) :
    ‖realMultiindexDeriv
      (fun x : Fin 3 ⊕ Fin 3 → ℝ => physicalKSAnalyticDescentA
        ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm) t0 (fun j => (x j : ℂ)))
      (Sum.elim α β) z‖ ≤ physicalKSDescentDerivativeBudget M A F0 W α β ∧
    ‖realMultiindexDeriv
      (fun x : Fin 3 ⊕ Fin 3 → ℝ => physicalKSAnalyticDescentB
        ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm) t0 (fun j => (x j : ℂ)))
      (Sum.elim α β) z‖ ≤
      (32*(7*physicalKSPointwiseRate M A)^2)*physicalKSDescentDerivativeBudget M A F0 W α β := by
  apply physicalKSAnalyticDescent_real_mixed_derivative_of_balanced hdata hA hF0 _ z hX hs α β
  intro m γ e he
  exact nuclearKSPhysicalTaylorSpectatorCoefficient_balanced_support g i hdata hA hF0
    (2*m) (Finsupp.equivFunOnFinite.symm γ) e he

theorem pairKSPhysicalAnalyticDescent_real_mixed_derivative
    (g : Configuration 2 → ℂ) {t0 : Position} {M A F0 W : ℝ}
    (hdata : PhysicalKSBoxPointwiseData
      ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm) t0 M A F0 W)
    (hA : 1 ≤ A) (hF0 : 0 ≤ F0)
    (z : Fin 3 ⊕ Fin 3 → ℝ)
    (hX : (32*(7*physicalKSPointwiseRate M A)^2)*‖fun j : Fin 3 => z (.inl j)‖ ≤ 1/4)
    (hs : (7*physicalKSPointwiseRate M A)*‖fun j : Fin 3 => z (.inr j)‖ ≤ 1/4)
    (α β : Fin 3 → ℕ) :
    ‖realMultiindexDeriv
      (fun x : Fin 3 ⊕ Fin 3 → ℝ => physicalKSAnalyticDescentA
        ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm) t0 (fun j => (x j : ℂ)))
      (Sum.elim α β) z‖ ≤ physicalKSDescentDerivativeBudget M A F0 W α β ∧
    ‖realMultiindexDeriv
      (fun x : Fin 3 ⊕ Fin 3 → ℝ => physicalKSAnalyticDescentB
        ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm) t0 (fun j => (x j : ℂ)))
      (Sum.elim α β) z‖ ≤
      (32*(7*physicalKSPointwiseRate M A)^2)*physicalKSDescentDerivativeBudget M A F0 W α β := by
  apply physicalKSAnalyticDescent_real_mixed_derivative_of_balanced hdata hA hF0 _ z hX hs α β
  intro m γ e he
  exact pairKSPhysicalTaylorSpectatorCoefficient_balanced_support g hdata hA hF0
    (2*m) (Finsupp.equivFunOnFinite.symm γ) e he

end TheoremT.Continuum
