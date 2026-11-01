import PhysicalKSAnalyticDescentSurjectivity_v1

/-! The same physical pointwise data, strengthened by analyticity of the
literal descended A/B sums and their actual physical-coordinate identity.
The complex convergence domain and physical neighborhood remain explicit. -/
set_option autoImplicit false
noncomputable section
namespace TheoremT.Continuum
open WeakGrushin

def PhysicalKSBoxAnalyticDescentData
    (f : Space (Fin 3) → ℂ) (v : Position → Position → ℂ)
    (t0 : Position) (M A F0 W : ℝ) : Prop :=
  PhysicalKSBoxPointwiseData f t0 M A F0 W ∧
  AnalyticOnNhd ℂ (physicalKSAnalyticDescentA f t0)
    {z : Fin 3 ⊕ Fin 3 → ℂ |
      (32*(7*physicalKSPointwiseRate M A)^2)*‖fun i : Fin 3 => z (.inl i)‖<1 ∧
      (7*physicalKSPointwiseRate M A)*‖fun i : Fin 3 => z (.inr i)‖<1} ∧
  AnalyticOnNhd ℂ (physicalKSAnalyticDescentB f t0)
    {z : Fin 3 ⊕ Fin 3 → ℂ |
      (32*(7*physicalKSPointwiseRate M A)^2)*‖fun i : Fin 3 => z (.inl i)‖<1 ∧
      (7*physicalKSPointwiseRate M A)*‖fun i : Fin 3 => z (.inr i)‖<1} ∧
  PhysicalKSAnalyticDescentOnPhysicalNeighborhood f v t0 M A

theorem nuclearKSPhysicalAnalyticDescent_data
    (g : Configuration 2 → ℂ) (i : Fin 2) {t0 : Position} {M A F0 W : ℝ}
    (hdata : PhysicalKSBoxPointwiseData
      ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm) t0 M A F0 W)
    (hA : 1≤A) (hF0 : 0≤F0) :
    PhysicalKSBoxAnalyticDescentData
      ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm)
      (fun X T => g (nuclearKSPhysicalCoordinates i X T)) t0 M A F0 W := by
  have han := nuclearKSPhysicalAnalyticDescent_analytic g i hdata hA hF0
  exact ⟨hdata,han.1,han.2,
    nuclearKSPhysicalAnalyticDescent_physical_neighborhood g i hdata hA hF0⟩

theorem pairKSPhysicalAnalyticDescent_data
    (g : Configuration 2 → ℂ) {t0 : Position} {M A F0 W : ℝ}
    (hdata : PhysicalKSBoxPointwiseData
      ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm) t0 M A F0 W)
    (hA : 1≤A) (hF0 : 0≤F0) :
    PhysicalKSBoxAnalyticDescentData
      ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm)
      (fun X T => g (pairKSPhysicalCoordinates X T)) t0 M A F0 W := by
  have han := pairKSPhysicalAnalyticDescent_analytic g hdata hA hF0
  exact ⟨hdata,han.1,han.2,
    pairKSPhysicalAnalyticDescent_physical_neighborhood g hdata hA hF0⟩

end TheoremT.Continuum
