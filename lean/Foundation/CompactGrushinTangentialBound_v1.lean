import GrushinFourierTangentialBound_v1
import PartialFourierIntegralTransfer_v1

noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators
namespace TheoremT.Continuum
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem compact_grushin_tangential_bound {c : ℝ} (hcn : 0 ≤ c)
    {G : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ κ → ℂ}
    (hG : ContDiff ℝ ∞ G) (hc : HasCompactSupport G) :
    (16*c) * (∑ k : κ,∫ p,‖partialTDirectional G (oscillatorBasis k) p‖^2
      ∂((volume : Measure (EuclideanSpace ℝ (Fin 4))).prod volume)) ≤
    ∫ p,‖euclideanGrushin c G p‖^2 ∂((volume : Measure (EuclideanSpace ℝ (Fin 4))).prod volume) := by
  have h := partialFourier_integrated_sum_le Finset.univ (fun _ : κ => 16*c) 1
    (fun k => partialTDirectional G (oscillatorBasis k))
    (fun k _ => partialTDirectional_contDiff hG _) (fun k _ => partialTDirectional_hasCompactSupport hc _)
    (euclideanGrushin_contDiff c hG) (euclideanGrushin_hasCompactSupport c hc)
    (fun ξ => by simpa only [one_mul] using grushin_fourier_tangential_bound hcn hG hc ξ)
  simpa only [one_mul,Finset.mul_sum] using h

#print axioms compact_grushin_tangential_bound
end TheoremT.Continuum
