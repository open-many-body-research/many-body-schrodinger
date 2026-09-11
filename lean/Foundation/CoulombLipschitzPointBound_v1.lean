import CoulombLocallyLipschitz_v1
import ContinuousAEBounds_v1

noncomputable section
open MeasureTheory
namespace TheoremT.Continuum

theorem scalar_coulomb_continuous_representative_bound {N : ℕ} (hN : 0 < N)
    {Z E : ℝ} {f : SpatialL2 N} (hg : scalarHamiltonianGraph N Z f ((E : ℂ) • f))
    {u : Configuration N → ℂ} (hu : Continuous u)
    (hEq : (f : Configuration N → ℂ) =ᵐ[volume] u) :
    ∀ x, ‖u x‖ ≤ coulombMoserBoundCoefficient N Z E*‖f‖ := by
  apply continuous_norm_bound_of_ae volume hu
  filter_upwards [hEq,scalar_coulomb_eigen_ae_bound hN hg] with x hx hb
  rwa [← hx]

theorem scalar_coulomb_bounded_locally_lipschitz_representative {N : ℕ} (hN : 0 < N)
    {Z E : ℝ} {f : SpatialL2 N} (hg : scalarHamiltonianGraph N Z f ((E : ℂ) • f)) :
    ∃ u : Configuration N → ℂ, LocallyLipschitz u ∧
      (f : Configuration N → ℂ) =ᵐ[volume] u ∧
      ∀ x, ‖u x‖ ≤ coulombMoserBoundCoefficient N Z E*‖f‖ := by
  obtain ⟨u,hu,hEq⟩ := scalar_coulomb_locally_lipschitz_representative hN hg
  exact ⟨u,hu,hEq,scalar_coulomb_continuous_representative_bound hN hg hu.continuous hEq⟩

#print axioms scalar_coulomb_continuous_representative_bound
#print axioms scalar_coulomb_bounded_locally_lipschitz_representative
end TheoremT.Continuum
