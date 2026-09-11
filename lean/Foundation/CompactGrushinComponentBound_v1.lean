import GrushinFourierComponentBound_v1
import PartialFourierIntegralTransfer_v1

noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators
namespace TheoremT.Continuum
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem compact_grushin_component_bound {c : ℝ} (hcn : 0 ≤ c)
    {G : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ κ → ℂ}
    (hG : ContDiff ℝ ∞ G) (hc : HasCompactSupport G) :
    (∫ p,‖grushinYLaplacian G p‖^2 ∂((volume : Measure (EuclideanSpace ℝ (Fin 4))).prod volume)) +
      (∫ p,‖grushinWeightedT c G p‖^2 ∂((volume : Measure (EuclideanSpace ℝ (Fin 4))).prod volume)) ≤
    (3/2 : ℝ) * (∫ p,‖euclideanGrushin c G p‖^2
      ∂((volume : Measure (EuclideanSpace ℝ (Fin 4))).prod volume)) := by
  have hY := partialFourier_fiber_norm_sq_integrable (grushinYLaplacian_contDiff hG)
    (grushinYLaplacian_hasCompactSupport hc)
  have hT := partialFourier_fiber_norm_sq_integrable (grushinWeightedT_contDiff c hG)
    (grushinWeightedT_hasCompactSupport c hc)
  have hP := partialFourier_fiber_norm_sq_integrable (euclideanGrushin_contDiff c hG)
    (euclideanGrushin_hasCompactSupport c hc)
  have h := integral_mono (hY.add hT) (hP.const_mul (3/2)) (grushin_fourier_component_bound hcn hG hc)
  simp only [Pi.add_apply] at h
  rw [integral_add hY hT,integral_const_mul] at h
  simpa only [partialFourier_plancherel_product (grushinYLaplacian_contDiff hG) (grushinYLaplacian_hasCompactSupport hc),
    partialFourier_plancherel_product (grushinWeightedT_contDiff c hG) (grushinWeightedT_hasCompactSupport c hc),
    partialFourier_plancherel_product (euclideanGrushin_contDiff c hG) (euclideanGrushin_hasCompactSupport c hc)] using h

#print axioms compact_grushin_component_bound
end TheoremT.Continuum
