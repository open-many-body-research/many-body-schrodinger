import GrushinFourierMixedBound_v1

noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators
namespace TheoremT.Continuum
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem compact_grushin_mixed_bound {c : ℝ} (hcn : 0 ≤ c)
    {G : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ κ → ℂ}
    (hG : ContDiff ℝ ∞ G) (hc : HasCompactSupport G) :
    2*c*(∑ i : Fin 4,∑ j : κ,∫ p,‖p.1‖^2 *
      ‖partialTDirectional (partialYDirectional G (oscillatorBasis i)) (oscillatorBasis j) p‖^2
      ∂((volume : Measure (EuclideanSpace ℝ (Fin 4))).prod volume)) ≤
    (3/2 : ℝ)*(∫ p,‖euclideanGrushin c G p‖^2
      ∂((volume : Measure (EuclideanSpace ℝ (Fin 4))).prod volume)) := by
  have h := partialFourier_weighted_integrated_sum_le continuous_norm
    (Finset.univ : Finset (Fin 4 × κ)) (fun _ => 2*c) (3/2)
    (fun k => partialTDirectional (partialYDirectional G (oscillatorBasis k.1)) (oscillatorBasis k.2))
    (fun k _ => partialTDirectional_contDiff (partialYDirectional_contDiff hG _) _)
    (fun k _ => partialTDirectional_hasCompactSupport (partialYDirectional_hasCompactSupport hc _) _)
    (euclideanGrushin_contDiff c hG) (euclideanGrushin_hasCompactSupport c hc)
    (fun ξ => by simpa only [Fintype.sum_prod_type,Finset.mul_sum] using grushin_fourier_mixed_bound hcn hG hc ξ)
  simpa only [Fintype.sum_prod_type,Finset.mul_sum] using h

#print axioms compact_grushin_mixed_bound
end TheoremT.Continuum
