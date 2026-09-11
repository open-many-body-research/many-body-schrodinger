import LocalBoundedGradientRepresentative_v1
import CoulombTransformedGradientBounded_v1

noncomputable section
open MeasureTheory
open scoped NNReal
namespace TheoremT.Continuum

theorem scalar_coulomb_transformed_lipschitz_representative_on_ball {N : ℕ} (hN : 0 < N)
    {Z E : ℝ} {f : SpatialL2 N} (hg : scalarHamiltonianGraph N Z f ((E : ℂ) • f))
    {A : ℝ} (hA : 0 < A) :
    ∃ K : ℝ≥0, ∃ u : Configuration N → ℂ,
      LipschitzWith K u ∧
      (fun x => Real.exp (-coulombCusp N Z x) • f x) =ᵐ[volume.restrict (Metric.ball 0 A)] u := by
  obtain ⟨g,a,b,hg2,hga,hab,hEq,hgt,hat⟩ :=
    scalar_coulomb_transformed_locally_bounded_weak_gradient hN hg (by positivity : 0 < 4*A)
  obtain ⟨K,u,hu,hgu⟩ := local_bounded_gradient_lipschitz_representative hA hga hab hgt hat
  have hμ : volume.restrict (Metric.ball (0 : Configuration N) A) ≤
      volume.restrict (Metric.ball 0 (4*A)) :=
    Measure.restrict_mono_set volume (Metric.ball_subset_ball (by linarith))
  exact ⟨K,u,hu,(hEq.filter_mono (ae_mono hμ)).symm.trans hgu⟩

#print axioms scalar_coulomb_transformed_lipschitz_representative_on_ball
end TheoremT.Continuum
