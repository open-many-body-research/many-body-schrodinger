import ManyBody.S8.Internal.NuclearChartScaling
import ManyBody.S8.Internal.NuclearPhysicalInitialization
import CoulombSpinNuclearKSOneStep_v1

/-! Quantitative initialization on an actual two-electron nuclear KS chart.
The potential bound, coefficient-patch inclusion, local L2 input and transformed
weak equation are proved from physical definitions and the eigenfunction graph.
The compact region and base constant precede Z, E and the spinful eigenfunction.
Only the displayed coefficient bound is uniform for 0 < r <= 1; the base constant
and compact region may depend on r, the center and the cutoff.
-/
noncomputable section
open MeasureTheory
open scoped Topology ContDiff BigOperators
open TheoremT.Continuum TheoremT.Continuum.WeakGrushin

namespace ManyBody.S8

theorem two_electron_scaled_nuclear_chart_initialization
    (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (t0 : Position) (ht0 : ‖t0‖ = r)
    {χ : NuclearKSSpace (0 : Fin 2) → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχΩ : tsupport χ ⊆ nuclearChartScaledOpen r t0) :
    ∃ K : Set (NuclearKSSpace (0 : Fin 2)), ∃ C : ℝ,
      IsCompact K ∧ tsupport χ ⊆ K ∧ K ⊆ nuclearChartScaledOpen r t0 ∧ 0 ≤ C ∧
      ∀ (Z E : ℝ) {ψ : SpinSpace 2}, hamiltonianGraph 2 Z ψ ((E : ℂ) • ψ) →
        ∃ u : SpinConfiguration 2 → Configuration 2 → ℂ,
          (∀ σ, LocallyLipschitz (u σ)) ∧
          (∀ᵐ x ∂volume, ∀ σ, ψ σ x = u σ x) ∧
          (∀ π : Equiv.Perm (Fin 2), ∀ σ, ∀ x,
            u (permuteSpin π σ) (permuteSpace π x) = permutationSign π • u σ x) ∧
          (∀ x, Real.sqrt (∑ σ : SpinConfiguration 2, ‖u σ x‖ ^ 2) ≤
            coulombMoserBoundCoefficient 2 Z E * ‖ψ‖) ∧
          ∀ σ : SpinConfiguration 2,
            let b : ℝ := (26 / 3 : ℝ) * |Z| + 8 / 11 + |E| / 2
            let F : ℝ := ∫ p in K, ‖u σ (nuclearKSLift (0 : Fin 2) p)‖ ^ 2
            ∃ U : Lp ℂ 2 (volume : Measure (NuclearKSSpace (0 : Fin 2))),
            ∃ gy : Fin 4 → Lp ℂ 2 (volume : Measure (NuclearKSSpace (0 : Fin 2))),
            ∃ gt : SpectatorCoordinate (0 : Fin 2) →
              Lp ℂ 2 (volume : Measure (NuclearKSSpace (0 : Fin 2))),
            ∃ hyy : Fin 4 → Fin 4 → Lp ℂ 2 (volume : Measure (NuclearKSSpace (0 : Fin 2))),
              U =ᵐ[volume] (fun p => χ p • u σ (nuclearKSLift (0 : Fin 2) p)) ∧
              (∑ j, ‖gy j‖ ^ 2) ≤ C * (11 / 4 + 3 / 4 * b ^ 2) * F ∧
              (∑ j, ‖gt j‖ ^ 2) ≤ (C * (1 + b ^ 2) * F) / 64 ∧
              (∑ j, ∑ k, ‖hyy j k‖ ^ 2) ≤ 3 / 2 * C * (1 + b ^ 2) * F ∧
              (∀ j, WeakProductL2Directional U (gy j) (yDir j)) ∧
              (∀ j, WeakProductL2Directional U (gt j) (tDir j)) ∧
              ∀ j k, WeakProductL2Directional (gy j) (hyy j k) (yDir k) := by
  obtain ⟨K, C, hK, hχK, hKΩ, hC, hgain⟩ :=
    scalar_nuclear_bounded_cutoff_gain (0 : Fin 2)
      (nuclearChartScaledOpen_isOpen r t0)
      (nuclearChartScaledOpen_subset_coefficientPatch r hr t0 ht0)
      hχ hcχ hχΩ
  refine ⟨K, C, hK, hχK, hKΩ, hC, ?_⟩
  intro Z E ψ hgraph
  obtain ⟨u, hu, hue, hperm, hbound⟩ :=
    coulomb_spin_locally_lipschitz_representative (by norm_num : 0 < (2 : ℕ)) hgraph
  refine ⟨u, hu, hue, hperm, hbound, ?_⟩
  intro σ
  have he : (ψ σ : Configuration 2 → ℂ) =ᵐ[volume] u σ := by
    filter_upwards [hue] with x hx
    exact hx σ
  have hb : 0 ≤ (26 / 3 : ℝ) * |Z| + 8 / 11 + |E| / 2 := by positivity
  have hBb : ∀ p ∈ K, ‖nuclearKSPotential (0 : Fin 2) Z E p‖ ≤
      (26 / 3 : ℝ) * |Z| + 8 / 11 + |E| / 2 := by
    intro p hp
    exact nuclearKSPotential_uniform_norm_le_of_mem_nuclearChartScaledOpen Z E r hr hr1 t0 ht0 (hKΩ hp)
  exact hgain Z E (hgraph.2.2 σ) (hu σ).continuous he
    ((26 / 3 : ℝ) * |Z| + 8 / 11 + |E| / 2) hb hBb

#print axioms two_electron_scaled_nuclear_chart_initialization
end ManyBody.S8
