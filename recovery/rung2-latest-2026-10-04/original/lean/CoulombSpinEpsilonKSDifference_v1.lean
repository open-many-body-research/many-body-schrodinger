import CoulombEpsilonKSDifference_v1
import CoulombSpinClassical_v1

/-! The actual normalized origin difference, component by component in full spin
space, satisfies both physical KS forcing equations for every positive scale. -/
noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators
namespace TheoremT.Continuum

theorem coulomb_spin_epsilon_KS_difference_representative
    {Z E : ℝ} {ψ : SpinSpace 2} (hg : hamiltonianGraph 2 Z ψ ((E : ℂ) • ψ)) :
    ∃ u : SpinConfiguration 2 → Configuration 2 → ℂ,
      (∀ σ, LocallyLipschitz (u σ)) ∧
      (∀ᵐ x ∂volume, ∀ σ, ψ σ x=u σ x) ∧
      (∀ π : Equiv.Perm (Fin 2), ∀ σ, ∀ x,
        u (permuteSpin π σ) (permuteSpace π x)=permutationSign π • u σ x) ∧
      (∀ x, Real.sqrt (∑ σ : SpinConfiguration 2, ‖u σ x‖^2) ≤
        coulombMoserBoundCoefficient 2 Z E*‖ψ‖) ∧
      ∀ σ, ∀ ε : ℝ, 0 < ε →
        (∀ i : Fin 2, ∀ φ : NuclearKSSpace i → ℝ,
          ContDiff ℝ ∞ φ → HasCompactSupport φ →
          tsupport φ ⊆ nuclearKSCoefficientPatch i →
          Integrable (fun q =>
            (splitGrushin 4 spectatorBasis (epsilonNuclearKSPotential i ε Z E) φ q : ℂ)*
              originScaledDifference (u σ) ε (nuclearKSLift i q)) volume ∧
          Integrable (fun q => φ q • (-(nuclearKSPotential i Z (ε*E) q • u σ 0))) volume ∧
          (∫ q, (splitGrushin 4 spectatorBasis (epsilonNuclearKSPotential i ε Z E) φ q : ℂ)*
            originScaledDifference (u σ) ε (nuclearKSLift i q))=
              ∫ q, φ q • (-(nuclearKSPotential i Z (ε*E) q • u σ 0))) ∧
        (∀ φ : PairKSSpace → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
          tsupport φ ⊆ pairKSCoefficientPatch →
          Integrable (fun q =>
            (splitGrushin 1 spectatorBasis (epsilonPairKSPotential ε Z E) φ q : ℂ)*
              originScaledDifference (u σ) ε (pairKSLift q)) volume ∧
          Integrable (fun q => φ q • (-(pairKSPotential Z (ε*E) q • u σ 0))) volume ∧
          (∫ q, (splitGrushin 1 spectatorBasis (epsilonPairKSPotential ε Z E) φ q : ℂ)*
            originScaledDifference (u σ) ε (pairKSLift q))=
              ∫ q, φ q • (-(pairKSPotential Z (ε*E) q • u σ 0))) := by
  obtain ⟨u,hu,hue,hperm,hbound⟩ :=
    coulomb_spin_locally_lipschitz_representative (by decide : 0 < 2) hg
  have he (σ : SpinConfiguration 2) : (ψ σ : Configuration 2 → ℂ) =ᵐ[volume] u σ := by
    filter_upwards [hue] with x hx
    exact hx σ
  refine ⟨u,hu,hue,hperm,hbound,?_⟩
  intro σ ε hε
  constructor
  · intro i φ hφ hc hs
    exact scalar_coulomb_epsilon_nuclear_KS_difference_weak i hε (hg.2.2 σ) (hu σ).continuous
      (he σ) hφ hc hs
  · intro φ hφ hc hs
    exact scalar_coulomb_epsilon_pair_KS_difference_weak hε (hg.2.2 σ) (hu σ).continuous
      (he σ) hφ hc hs

#print axioms coulomb_spin_epsilon_KS_difference_representative
end TheoremT.Continuum
