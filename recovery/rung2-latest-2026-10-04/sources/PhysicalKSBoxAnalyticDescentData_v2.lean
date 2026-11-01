import PhysicalKSBoxAnalyticDescentData_v1
import PhysicalKSAnalyticDescentRealDerivative_v1

/-! The preceding actual physical decomposition is retained together with
literal complex and real mixed coordinate derivatives of its same A/B sums.
Derivative bounds use coordinate sup norms on the closed quarter product
polydisc; the physical identity keeps its original Euclidean neighborhood. -/
set_option autoImplicit false
noncomputable section
namespace TheoremT.Continuum
open WeakGrushin

def PhysicalKSBoxAnalyticDescentDerivativeData
    (f : Space (Fin 3) → ℂ) (v : Position → Position → ℂ)
    (t0 : Position) (M A F0 W : ℝ) : Prop :=
  PhysicalKSBoxAnalyticDescentData f v t0 M A F0 W ∧
  (∀ z : Fin 3 ⊕ Fin 3 → ℂ,
    (32*(7*physicalKSPointwiseRate M A)^2)*‖fun i : Fin 3 => z (.inl i)‖ ≤ 1/4 →
    (7*physicalKSPointwiseRate M A)*‖fun i : Fin 3 => z (.inr i)‖ ≤ 1/4 →
    ∀ α β : Fin 3 → ℕ,
    ‖complexMultiindexDeriv (physicalKSAnalyticDescentA f t0) (Sum.elim α β) z‖ ≤
      physicalKSDescentDerivativeBudget M A F0 W α β ∧
    ‖complexMultiindexDeriv (physicalKSAnalyticDescentB f t0) (Sum.elim α β) z‖ ≤
      (32*(7*physicalKSPointwiseRate M A)^2)*physicalKSDescentDerivativeBudget M A F0 W α β) ∧
  (∀ z : Fin 3 ⊕ Fin 3 → ℝ,
    (32*(7*physicalKSPointwiseRate M A)^2)*‖fun i : Fin 3 => z (.inl i)‖ ≤ 1/4 →
    (7*physicalKSPointwiseRate M A)*‖fun i : Fin 3 => z (.inr i)‖ ≤ 1/4 →
    ∀ α β : Fin 3 → ℕ,
    ‖realMultiindexDeriv
      (fun x : Fin 3 ⊕ Fin 3 → ℝ => physicalKSAnalyticDescentA f t0 (fun i => (x i : ℂ)))
      (Sum.elim α β) z‖ ≤ physicalKSDescentDerivativeBudget M A F0 W α β ∧
    ‖realMultiindexDeriv
      (fun x : Fin 3 ⊕ Fin 3 → ℝ => physicalKSAnalyticDescentB f t0 (fun i => (x i : ℂ)))
      (Sum.elim α β) z‖ ≤
      (32*(7*physicalKSPointwiseRate M A)^2)*physicalKSDescentDerivativeBudget M A F0 W α β)

theorem nuclearKSPhysicalAnalyticDescent_derivative_data
    (g : Configuration 2 → ℂ) (i : Fin 2) {t0 : Position} {M A F0 W : ℝ}
    (hdata : PhysicalKSBoxPointwiseData
      ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm) t0 M A F0 W)
    (hA : 1≤A) (hF0 : 0≤F0) :
    PhysicalKSBoxAnalyticDescentDerivativeData
      ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm)
      (fun X T => g (nuclearKSPhysicalCoordinates i X T)) t0 M A F0 W := by
  refine ⟨nuclearKSPhysicalAnalyticDescent_data g i hdata hA hF0, ?_, ?_⟩
  · intro z hX hs α β
    exact nuclearKSPhysicalAnalyticDescent_mixed_derivative g i hdata hA hF0 z hX hs α β
  · intro z hX hs α β
    exact nuclearKSPhysicalAnalyticDescent_real_mixed_derivative g i hdata hA hF0 z hX hs α β

theorem pairKSPhysicalAnalyticDescent_derivative_data
    (g : Configuration 2 → ℂ) {t0 : Position} {M A F0 W : ℝ}
    (hdata : PhysicalKSBoxPointwiseData
      ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm) t0 M A F0 W)
    (hA : 1≤A) (hF0 : 0≤F0) :
    PhysicalKSBoxAnalyticDescentDerivativeData
      ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm)
      (fun X T => g (pairKSPhysicalCoordinates X T)) t0 M A F0 W := by
  refine ⟨pairKSPhysicalAnalyticDescent_data g hdata hA hF0, ?_, ?_⟩
  · intro z hX hs α β
    exact pairKSPhysicalAnalyticDescent_mixed_derivative g hdata hA hF0 z hX hs α β
  · intro z hX hs α β
    exact pairKSPhysicalAnalyticDescent_real_mixed_derivative g hdata hA hF0 z hX hs α β

end TheoremT.Continuum
