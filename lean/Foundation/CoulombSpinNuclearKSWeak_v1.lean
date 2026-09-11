import CoulombNuclearKSWeak_v1
import CoulombSpinClassical_v1

noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators
namespace TheoremT.Continuum

theorem coulomb_spin_nuclear_KS_weak_representative {N : ℕ} (hN : 0 < N)
    {Z E : ℝ} {ψ : SpinSpace N} (hg : hamiltonianGraph N Z ψ ((E : ℂ) • ψ)) :
    ∃ u : SpinConfiguration N → Configuration N → ℂ,
      (∀ σ, LocallyLipschitz (u σ)) ∧
      (∀ᵐ x ∂volume, ∀ σ, ψ σ x=u σ x) ∧
      (∀ π : Equiv.Perm (Fin N), ∀ σ, ∀ x,
        u (permuteSpin π σ) (permuteSpace π x)=permutationSign π • u σ x) ∧
      (∀ x, Real.sqrt (∑ σ : SpinConfiguration N, ‖u σ x‖^2) ≤
        coulombMoserBoundCoefficient N Z E*‖ψ‖) ∧
      ∀ σ (i : Fin N), LocallyLipschitz (u σ ∘ nuclearKSLift i) ∧
        ∀ φ : NuclearKSSpace i → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
          tsupport φ ⊆ nuclearKSCoefficientPatch i →
          Integrable (fun q => (splitGrushin 4 spectatorBasis (nuclearKSPotential i Z E) φ q : ℂ)*
            (u σ ∘ nuclearKSLift i) q) volume ∧
          (∫ q, (splitGrushin 4 spectatorBasis (nuclearKSPotential i Z E) φ q : ℂ)*
            (u σ ∘ nuclearKSLift i) q)=0 := by
  obtain ⟨u,hu,hue,hperm,hbound⟩ := coulomb_spin_locally_lipschitz_representative hN hg
  have he (σ : SpinConfiguration N) : (ψ σ : Configuration N → ℂ) =ᵐ[volume] u σ := by
    filter_upwards [hue] with x hx
    exact hx σ
  refine ⟨u,hu,hue,hperm,hbound,?_⟩
  intro σ i
  exact ⟨(hu σ).comp (nuclearKSLift_locallyLipschitz i),
    fun φ hφ hc hs => scalar_coulomb_nuclear_KS_weak i (hg.2.2 σ) (hu σ).continuous
      (he σ) hφ hc hs⟩

#print axioms coulomb_spin_nuclear_KS_weak_representative
end TheoremT.Continuum
