import CoulombPointwiseEquation_v1
import CoulombSpinLocallyLipschitz_v1

noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators
namespace TheoremT.Continuum

theorem coulomb_spin_classical_representative {N : ℕ} (hN : 0 < N)
    {Z E : ℝ} {ψ : SpinSpace N} (hg : hamiltonianGraph N Z ψ ((E : ℂ) • ψ)) :
    ∃ u : SpinConfiguration N → Configuration N → ℂ,
      (∀ σ, LocallyLipschitz (u σ)) ∧
      (∀ᵐ x ∂volume, ∀ σ, ψ σ x=u σ x) ∧
      (∀ π : Equiv.Perm (Fin N), ∀ σ, ∀ x,
        u (permuteSpin π σ) (permuteSpace π x)=permutationSign π • u σ x) ∧
      (∀ x, Real.sqrt (∑ σ : SpinConfiguration N, ‖u σ x‖^2) ≤
        coulombMoserBoundCoefficient N Z E*‖ψ‖) ∧
      ∀ σ x, collisionFree x → ContDiffAt ℝ ∞ (u σ) x ∧
        smoothLaplacian (u σ) x=2*((coulombPotential N Z x : ℂ)-(E:ℂ))*u σ x := by
  obtain ⟨u,hu,hue,hperm,hbound⟩ := coulomb_spin_locally_lipschitz_representative hN hg
  have he (σ : SpinConfiguration N) : (ψ σ : Configuration N → ℂ) =ᵐ[volume] u σ := by
    filter_upwards [hue] with x hx
    exact hx σ
  refine ⟨u,hu,hue,hperm,hbound,?_⟩
  intro σ x hx
  exact ⟨scalar_coulomb_continuous_rep_smooth_away (hg.2.2 σ) (hu σ).continuous (he σ) hx,
    scalar_coulomb_continuous_rep_pointwise_equation (hg.2.2 σ) (hu σ).continuous (he σ) hx⟩

#print axioms coulomb_spin_classical_representative
end TheoremT.Continuum
