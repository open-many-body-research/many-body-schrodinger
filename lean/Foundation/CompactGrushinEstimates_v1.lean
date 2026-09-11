import CompactGrushinComponentBound_v1
import CompactGrushinTangentialBound_v1
import CompactGrushinMixedBound_v1

noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators
namespace TheoremT.Continuum
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem compact_grushin_estimates {c : ℝ} (hcn : 0 ≤ c)
    {G : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ κ → ℂ}
    (hG : ContDiff ℝ ∞ G) (hc : HasCompactSupport G) :
    ((16*c) * (∑ j : κ,∫ p,‖partialTDirectional G (oscillatorBasis j) p‖^2
      ∂((volume : Measure (EuclideanSpace ℝ (Fin 4))).prod volume)) ≤
      ∫ p,‖euclideanGrushin c G p‖^2 ∂((volume : Measure (EuclideanSpace ℝ (Fin 4))).prod volume)) ∧
    ((∫ p,‖grushinYLaplacian G p‖^2 ∂((volume : Measure (EuclideanSpace ℝ (Fin 4))).prod volume)) +
      (∫ p,‖grushinWeightedT c G p‖^2 ∂((volume : Measure (EuclideanSpace ℝ (Fin 4))).prod volume)) ≤
      (3/2 : ℝ) * (∫ p,‖euclideanGrushin c G p‖^2
        ∂((volume : Measure (EuclideanSpace ℝ (Fin 4))).prod volume))) ∧
    (2*c*(∑ i : Fin 4,∑ j : κ,∫ p,‖p.1‖^2 *
      ‖partialTDirectional (partialYDirectional G (oscillatorBasis i)) (oscillatorBasis j) p‖^2
      ∂((volume : Measure (EuclideanSpace ℝ (Fin 4))).prod volume)) ≤
      (3/2 : ℝ)*(∫ p,‖euclideanGrushin c G p‖^2
        ∂((volume : Measure (EuclideanSpace ℝ (Fin 4))).prod volume))) :=
  ⟨compact_grushin_tangential_bound hcn hG hc,compact_grushin_component_bound hcn hG hc,
    compact_grushin_mixed_bound hcn hG hc⟩

#print axioms compact_grushin_estimates
end TheoremT.Continuum
