import CoulombPairKSWeak_v1
import CoulombSpinClassical_v1

/-! Pair KS weak equation for every component of the actual full N=2 fermionic
spin-space eigenfunction, using one simultaneous representative family. -/
noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators
namespace TheoremT.Continuum

theorem coulomb_spin_pair_KS_weak_representative
    {Z E : ℝ} {ψ : SpinSpace 2} (hg : hamiltonianGraph 2 Z ψ ((E : ℂ) • ψ)) :
    ∃ u : SpinConfiguration 2 → Configuration 2 → ℂ,
      (∀ σ, LocallyLipschitz (u σ)) ∧
      (∀ᵐ x ∂volume, ∀ σ, ψ σ x=u σ x) ∧
      (∀ π : Equiv.Perm (Fin 2), ∀ σ, ∀ x,
        u (permuteSpin π σ) (permuteSpace π x)=permutationSign π • u σ x) ∧
      (∀ x, Real.sqrt (∑ σ : SpinConfiguration 2, ‖u σ x‖^2) ≤
        coulombMoserBoundCoefficient 2 Z E*‖ψ‖) ∧
      ∀ σ, LocallyLipschitz (u σ ∘ pairKSLift) ∧
        ∀ φ : PairKSSpace → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
          tsupport φ ⊆ pairKSCoefficientPatch →
          Integrable (fun q => (splitGrushin 1 spectatorBasis (pairKSPotential Z E) φ q : ℂ)*
            (u σ ∘ pairKSLift) q) volume ∧
          (∫ q, (splitGrushin 1 spectatorBasis (pairKSPotential Z E) φ q : ℂ)*
            (u σ ∘ pairKSLift) q)=0 := by
  obtain ⟨u,hu,hue,hperm,hbound⟩ :=
    coulomb_spin_locally_lipschitz_representative (by decide : 0 < 2) hg
  have he (σ : SpinConfiguration 2) : (ψ σ : Configuration 2 → ℂ) =ᵐ[volume] u σ := by
    filter_upwards [hue] with x hx
    exact hx σ
  refine ⟨u,hu,hue,hperm,hbound,?_⟩
  intro σ
  exact ⟨(hu σ).comp pairKSLift_locallyLipschitz,
    fun φ hφ hc hs => scalar_coulomb_pair_KS_weak (hg.2.2 σ) (hu σ).continuous
      (he σ) hφ hc hs⟩

#print axioms coulomb_spin_pair_KS_weak_representative
end TheoremT.Continuum
