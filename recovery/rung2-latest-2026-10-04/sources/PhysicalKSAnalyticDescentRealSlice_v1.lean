import PhysicalKSTaylorAnalyticDescentData_v1
import RealPositionSpectatorSliceAnalytic_v1

/-! Actual physical Position-domain real analytic slices of the nuclear
and pair A/B functions. The ball uses the physical Euclidean spatial norm.
The fixed spectator is also a Position, with its Euclidean norm bounded
against the actual spectator rate. -/
noncomputable section
set_option autoImplicit false
namespace TheoremT.Continuum

theorem nuclearKSPhysicalAnalyticDescent_real_position_slices
    (g : Configuration 2 → ℂ) (i : Fin 2) {t0 : Position} {M A F0 W : ℝ}
    (hdata : PhysicalKSBoxPointwiseData
      ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm) t0 M A F0 W)
    (hA : 1 ≤ A) (hF0 : 0 ≤ F0) (T : Position)
    (hT : (7*physicalKSPointwiseRate M A)*‖T‖ < 1) :
    AnalyticOnNhd ℝ
      (fun X : Position => physicalKSAnalyticDescentA
        ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm) t0
        (Sum.elim (fun j => (X j : ℂ)) (fun j => (T j : ℂ))))
      (Metric.ball (0 : Position) (32*(7*physicalKSPointwiseRate M A)^2)⁻¹) ∧
    AnalyticOnNhd ℝ
      (fun X : Position => physicalKSAnalyticDescentB
        ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm) t0
        (Sum.elim (fun j => (X j : ℂ)) (fun j => (T j : ℂ))))
      (Metric.ball (0 : Position) (32*(7*physicalKSPointwiseRate M A)^2)⁻¹) := by
  have hS : 0 < 7*physicalKSPointwiseRate M A :=
    mul_pos (by norm_num) (physicalKSPointwiseRate_pos hA)
  have hD : 0 < 32*(7*physicalKSPointwiseRate M A)^2 := by positivity
  have hana := nuclearKSPhysicalAnalyticDescent_analytic g i hdata hA hF0
  exact ⟨real_position_fixed_spectator_slice_analyticOnNhd_ball _ hD hS.le hana.1 T hT,
    real_position_fixed_spectator_slice_analyticOnNhd_ball _ hD hS.le hana.2 T hT⟩

theorem pairKSPhysicalAnalyticDescent_real_position_slices
    (g : Configuration 2 → ℂ) {t0 : Position} {M A F0 W : ℝ}
    (hdata : PhysicalKSBoxPointwiseData
      ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm) t0 M A F0 W)
    (hA : 1 ≤ A) (hF0 : 0 ≤ F0) (T : Position)
    (hT : (7*physicalKSPointwiseRate M A)*‖T‖ < 1) :
    AnalyticOnNhd ℝ
      (fun X : Position => physicalKSAnalyticDescentA
        ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm) t0
        (Sum.elim (fun j => (X j : ℂ)) (fun j => (T j : ℂ))))
      (Metric.ball (0 : Position) (32*(7*physicalKSPointwiseRate M A)^2)⁻¹) ∧
    AnalyticOnNhd ℝ
      (fun X : Position => physicalKSAnalyticDescentB
        ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm) t0
        (Sum.elim (fun j => (X j : ℂ)) (fun j => (T j : ℂ))))
      (Metric.ball (0 : Position) (32*(7*physicalKSPointwiseRate M A)^2)⁻¹) := by
  have hS : 0 < 7*physicalKSPointwiseRate M A :=
    mul_pos (by norm_num) (physicalKSPointwiseRate_pos hA)
  have hD : 0 < 32*(7*physicalKSPointwiseRate M A)^2 := by positivity
  have hana := pairKSPhysicalAnalyticDescent_analytic g hdata hA hF0
  exact ⟨real_position_fixed_spectator_slice_analyticOnNhd_ball _ hD hS.le hana.1 T hT,
    real_position_fixed_spectator_slice_analyticOnNhd_ball _ hD hS.le hana.2 T hT⟩

end TheoremT.Continuum
