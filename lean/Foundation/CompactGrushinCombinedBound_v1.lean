import GrushinFourierCombinedBound_v1

noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators
namespace TheoremT.Continuum
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem compact_grushin_combined_bound {c : ℝ} (hcn : 0 ≤ c)
    {G : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ κ → ℂ}
    (hG : ContDiff ℝ ∞ G) (hc : HasCompactSupport G) :
    (∫ p,‖grushinYLaplacian G p‖^2 ∂((volume : Measure (EuclideanSpace ℝ (Fin 4))).prod volume)) +
      (∫ p,‖grushinWeightedT c G p‖^2 ∂((volume : Measure (EuclideanSpace ℝ (Fin 4))).prod volume)) +
      2*c*(∑ i : Fin 4,∑ j : κ,∫ p,‖p.1‖^2 *
        ‖partialTDirectional (partialYDirectional G (oscillatorBasis i)) (oscillatorBasis j) p‖^2
        ∂((volume : Measure (EuclideanSpace ℝ (Fin 4))).prod volume)) ≤
      (3/2 : ℝ)*(∫ p,‖euclideanGrushin c G p‖^2
        ∂((volume : Measure (EuclideanSpace ℝ (Fin 4))).prod volume)) := by
  have hY := partialFourier_fiber_norm_sq_integrable (grushinYLaplacian_contDiff hG)
    (grushinYLaplacian_hasCompactSupport hc)
  have hT := partialFourier_fiber_norm_sq_integrable (grushinWeightedT_contDiff c hG)
    (grushinWeightedT_hasCompactSupport c hc)
  have hP := partialFourier_fiber_norm_sq_integrable (euclideanGrushin_contDiff c hG)
    (euclideanGrushin_hasCompactSupport c hc)
  have hI (i : Fin 4) (j : κ) :=
    (partialFourier_weighted_plancherel continuous_norm
      (partialTDirectional_contDiff (partialYDirectional_contDiff hG (oscillatorBasis i)) (oscillatorBasis j))
      (partialTDirectional_hasCompactSupport (partialYDirectional_hasCompactSupport hc (oscillatorBasis i)) (oscillatorBasis j))).1
  have hM := integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hI i j))
  have hYT : Integrable (fun ξ =>
      (∫ y,‖partialFourier (grushinYLaplacian G) ξ y‖^2) +
      (∫ y,‖partialFourier (grushinWeightedT c G) ξ y‖^2)) volume := hY.add hT
  have h := integral_mono (hYT.add (hM.const_mul (2*c))) (hP.const_mul (3/2))
    (grushin_fourier_combined_bound hcn hG hc)
  simp only [Pi.add_apply] at h
  rw [integral_add hYT (hM.const_mul (2*c)),integral_add hY hT,
    integral_const_mul,integral_const_mul] at h
  have he :
      (∫ ξ,∑ i : Fin 4,∑ j : κ,∫ y,‖y‖^2 *
        ‖partialFourier (partialTDirectional (partialYDirectional G (oscillatorBasis i)) (oscillatorBasis j)) ξ y‖^2) =
      ∑ i : Fin 4,∑ j : κ,∫ p,‖p.1‖^2 *
        ‖partialTDirectional (partialYDirectional G (oscillatorBasis i)) (oscillatorBasis j) p‖^2
        ∂((volume : Measure (EuclideanSpace ℝ (Fin 4))).prod volume) := by
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hI i j))]
    simp_rw [integral_finsetSum _ (fun j _ => hI _ j)]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact (partialFourier_weighted_plancherel continuous_norm
      (partialTDirectional_contDiff (partialYDirectional_contDiff hG (oscillatorBasis i)) (oscillatorBasis j))
      (partialTDirectional_hasCompactSupport (partialYDirectional_hasCompactSupport hc (oscillatorBasis i)) (oscillatorBasis j))).2
  rw [he] at h
  simpa only [partialFourier_plancherel_product (grushinYLaplacian_contDiff hG) (grushinYLaplacian_hasCompactSupport hc),
    partialFourier_plancherel_product (grushinWeightedT_contDiff c hG) (grushinWeightedT_hasCompactSupport c hc),
    partialFourier_plancherel_product (euclideanGrushin_contDiff c hG) (euclideanGrushin_hasCompactSupport c hc)] using h

#print axioms compact_grushin_combined_bound
end TheoremT.Continuum
