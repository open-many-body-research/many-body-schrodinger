import CoulombLipschitzBall_v1
import LocalRepresentativeGluing_v1

/-! Actual scalar Coulomb H2 eigenfunctions have a unique locally Lipschitz
representative on the whole configuration space, including every collision. -/
noncomputable section
open MeasureTheory
namespace TheoremT.Continuum

theorem scalar_coulomb_locally_lipschitz_representative {N : ℕ} (hN : 0 < N)
    {Z E : ℝ} {f : SpatialL2 N} (hg : scalarHamiltonianGraph N Z f ((E : ℂ) • f)) :
    ∃ u : Configuration N → ℂ, LocallyLipschitz u ∧ (f : Configuration N → ℂ) =ᵐ[volume] u := by
  have hex (n : ℕ) : ∃ u : Configuration N → ℂ, LocallyLipschitz u ∧
      (f : Configuration N → ℂ) =ᵐ[volume.restrict (Metric.ball 0 ((n:ℝ)+1))] u :=
    scalar_coulomb_lipschitz_representative_on_ball hN hg (by positivity)
  choose v hv hEq using hex
  apply locally_lipschitz_representatives_glue volume (fun n => Metric.isOpen_ball) _ hv hEq
  intro x
  obtain ⟨n,hn⟩ := exists_nat_gt ‖x‖
  exact ⟨n,mem_ball_zero_iff.mpr (by linarith)⟩

theorem scalar_coulomb_unique_locally_lipschitz_representative {N : ℕ} (hN : 0 < N)
    {Z E : ℝ} {f : SpatialL2 N} (hg : scalarHamiltonianGraph N Z f ((E : ℂ) • f)) :
    ∃! u : Configuration N → ℂ, LocallyLipschitz u ∧ (f : Configuration N → ℂ) =ᵐ[volume] u := by
  obtain ⟨u,hu,heu⟩ := scalar_coulomb_locally_lipschitz_representative hN hg
  refine ⟨u,⟨hu,heu⟩,?_⟩
  intro v hv
  exact volume.eq_of_ae_eq (hv.2.symm.trans heu) hv.1.continuous hu.continuous

#print axioms scalar_coulomb_locally_lipschitz_representative
#print axioms scalar_coulomb_unique_locally_lipschitz_representative
end TheoremT.Continuum
