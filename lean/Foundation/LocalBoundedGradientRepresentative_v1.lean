import WeakBoundedGradientRepresentative_v1
import CompactCutoffBoundedGradient_v1

noncomputable section
open MeasureTheory
open scoped NNReal
namespace TheoremT.Continuum

theorem local_bounded_gradient_lipschitz_representative {N : ℕ} {A : ℝ} (hA : 0 < A)
    {f : SpatialL2 N} {d : Coordinate N → SpatialL2 N}
    {e : Coordinate N → Coordinate N → SpatialL2 N}
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k l, WeakPartial (d k) (e k l) l)
    (hf : MemLp f ⊤ (volume.restrict (Metric.ball 0 (4*A))))
    (hdt : ∀ k, MemLp (d k) ⊤ (volume.restrict (Metric.ball 0 (4*A)))) :
    ∃ K : ℝ≥0, ∃ u : Configuration N → ℂ,
      LipschitzWith K u ∧
      (f : Configuration N → ℂ) =ᵐ[volume.restrict (Metric.ball 0 A)] u := by
  obtain ⟨v,a,hva,hat,hEq⟩ := cutoff_globally_bounded_weak_gradient hA hd he hf hdt
  obtain ⟨K,u,hu,hvu⟩ := weak_bounded_gradient_lipschitz_representative v a hva hat
  exact ⟨K,u,hu,hEq.symm.trans (hvu.filter_mono (ae_mono Measure.restrict_le_self))⟩

#print axioms local_bounded_gradient_lipschitz_representative
end TheoremT.Continuum
