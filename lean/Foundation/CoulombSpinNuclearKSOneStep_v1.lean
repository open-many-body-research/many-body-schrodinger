import CoulombNuclearKSOneStep_v1
import CoulombSpinNuclearKSWeak_v1

/-! One physical spin representative, with its simultaneous permutation law,
has actual localized nuclear-KS Y/T/YY weak jets in every spin component.
The compact region and constant are shared by all spin components. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace TheoremT.Continuum

theorem coulomb_spin_nuclear_KS_one_step_representative {N : ℕ} (hN : 0 < N)
    {Z E : ℝ} {ψ : SpinSpace N} (hg : hamiltonianGraph N Z ψ ((E : ℂ) • ψ)) :
    ∃ u : SpinConfiguration N → Configuration N → ℂ,
      (∀ σ, LocallyLipschitz (u σ)) ∧
      (∀ᵐ x ∂volume, ∀ σ, ψ σ x = u σ x) ∧
      (∀ π : Equiv.Perm (Fin N), ∀ σ, ∀ x,
        u (permuteSpin π σ) (permuteSpace π x) = permutationSign π • u σ x) ∧
      (∀ x, Real.sqrt (∑ σ : SpinConfiguration N, ‖u σ x‖^2) ≤
        coulombMoserBoundCoefficient N Z E*‖ψ‖) ∧
      ∀ (i : Fin N) (χ : NuclearKSSpace i → ℝ),
        ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ nuclearKSCoefficientPatch i →
        ∃ K : Set (NuclearKSSpace i), ∃ C : ℝ,
          IsCompact K ∧ tsupport χ ⊆ K ∧ K ⊆ nuclearKSCoefficientPatch i ∧ 0 ≤ C ∧
          ∀ σ : SpinConfiguration N,
            let F : ℝ := ∫ p in K, ‖u σ (nuclearKSLift i p)‖^2
            let M : ℝ := ∫ p in K, ‖nuclearKSPotential i Z E p • u σ (nuclearKSLift i p)‖^2
            ∃ U : Lp ℂ 2 (volume : Measure (NuclearKSSpace i)),
            ∃ gy : Fin 4 → Lp ℂ 2 (volume : Measure (NuclearKSSpace i)),
            ∃ gt : SpectatorCoordinate i → Lp ℂ 2 (volume : Measure (NuclearKSSpace i)),
            ∃ hyy : Fin 4 → Fin 4 → Lp ℂ 2 (volume : Measure (NuclearKSSpace i)),
              U =ᵐ[volume] (fun p => χ p • u σ (nuclearKSLift i p)) ∧
              (∑ j, ‖gy j‖^2) ≤ 2*(C*F)+(3/4 : ℝ)*(C*(F+M)) ∧
              (∑ j, ‖gt j‖^2) ≤ (C*(F+M))/64 ∧
              (∑ j, ∑ k, ‖hyy j k‖^2) ≤ (3/2 : ℝ)*(C*(F+M)) ∧
              (∀ j, WeakProductL2Directional U (gy j) (WeakGrushin.yDir j)) ∧
              (∀ j, WeakProductL2Directional U (gt j) (WeakGrushin.tDir j)) ∧
              ∀ j k, WeakProductL2Directional (gy j) (hyy j k) (WeakGrushin.yDir k) := by
  obtain ⟨u,hu,hue,hperm,hbound⟩ := coulomb_spin_locally_lipschitz_representative hN hg
  refine ⟨u,hu,hue,hperm,hbound,?_⟩
  intro i χ hχ hcχ hsχ
  obtain ⟨K,C,hK,hχK,hKΩ,hC,hgain⟩ := scalar_coulomb_nuclear_KS_one_step i Z E hχ hcχ hsχ
  refine ⟨K,C,hK,hχK,hKΩ,hC,?_⟩
  intro σ
  have he : (ψ σ : Configuration N → ℂ) =ᵐ[volume] u σ := by
    filter_upwards [hue] with x hx
    exact hx σ
  exact hgain (hg.2.2 σ) (hu σ).continuous he

#print axioms coulomb_spin_nuclear_KS_one_step_representative
end TheoremT.Continuum
