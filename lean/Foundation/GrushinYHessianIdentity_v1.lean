import CompactFiniteHessianIdentity_v1
import CompactSpectatorCutoffEnergy_v1
import CompactGrushinCombinedBound_v1

noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators
namespace TheoremT.Continuum
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem compact_grushin_y_hessian_identity
    {G : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → ℂ}
    (hG : ContDiff ℝ ∞ G) (hc : HasCompactSupport G) :
    (∫ p, ‖grushinYLaplacian G p‖^2
      ∂((volume : Measure (EuclideanSpace ℝ ι)).prod volume)) =
      ∑ i : ι, ∑ j : ι, ∫ p,
        ‖partialYDirectional (partialYDirectional G (oscillatorBasis i)) (oscillatorBasis j) p‖^2
        ∂((volume : Measure (EuclideanSpace ℝ ι)).prod volume) := by
  letI := euclidean_product_volume_isAddHaar (ι := ι) (κ := κ)
  exact compact_finite_hessian_identity hG hc (fun i : ι => (oscillatorBasis i,0))

theorem compact_grushin_full_y_hessian_bound {c : ℝ} (hcn : 0 ≤ c)
    {G : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ κ → ℂ}
    (hG : ContDiff ℝ ∞ G) (hc : HasCompactSupport G) :
    (∑ i : Fin 4, ∑ j : Fin 4, ∫ p,
      ‖partialYDirectional (partialYDirectional G (oscillatorBasis i)) (oscillatorBasis j) p‖^2
        ∂((volume : Measure (EuclideanSpace ℝ (Fin 4))).prod volume)) +
      (∫ p,‖grushinWeightedT c G p‖^2
        ∂((volume : Measure (EuclideanSpace ℝ (Fin 4))).prod volume)) +
      2*c*(∑ i : Fin 4,∑ j : κ,∫ p,‖p.1‖^2 *
        ‖partialTDirectional (partialYDirectional G (oscillatorBasis i)) (oscillatorBasis j) p‖^2
        ∂((volume : Measure (EuclideanSpace ℝ (Fin 4))).prod volume)) ≤
      (3/2 : ℝ)*(∫ p,‖euclideanGrushin c G p‖^2
        ∂((volume : Measure (EuclideanSpace ℝ (Fin 4))).prod volume)) := by
  rw [← compact_grushin_y_hessian_identity hG hc]
  exact compact_grushin_combined_bound hcn hG hc

#print axioms compact_grushin_y_hessian_identity
#print axioms compact_grushin_full_y_hessian_bound
end TheoremT.Continuum
