import ManyBody.S8.NuclearChartInitialization
import ManyBody.S8.Internal.PhysicalPlateauEquation
import ManyBody.S8.Internal.SpectatorBootstrap
import ManyBody.S8.Internal.SpectatorForcingBudget
import LocalWeakGrushinPlateau_v1

/-! A physical first spectator bootstrap, with no input derivative hypothesis.
Outer initialization supplies the first spectator derivatives. Plateau locality
then supplies their actual differentiated weak equations and the inner gain.
The literal principal forcing budget is bounded by the proved coefficient and
spectator-derivative bounds. No H12 or factorial estimate is asserted here.
-/
noncomputable section
open MeasureTheory
open scoped Topology ContDiff BigOperators
open TheoremT.Continuum TheoremT.Continuum.WeakGrushin

namespace ManyBody.S8

theorem two_electron_nuclear_chart_spectator_bootstrap
    (t0 : Position) (ht0 : ‖t0‖ = 1)
    {χ : NuclearKSSpace (0 : Fin 2) → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχΩ : tsupport χ ⊆ nuclearChartOpen t0) :
    ∃ χouter : NuclearKSSpace (0 : Fin 2) → ℝ,
      ContDiff ℝ ∞ χouter ∧ HasCompactSupport χouter ∧
      tsupport χouter ⊆ nuclearChartOpen t0 ∧
    ∃ V : Set (NuclearKSSpace (0 : Fin 2)),
      IsOpen V ∧ tsupport χ ⊆ V ∧ V ⊆ nuclearChartOpen t0 ∧
      (∀ p ∈ V, χouter p = 1) ∧
    ∃ K : Set (NuclearKSSpace (0 : Fin 2)), ∃ C : ℝ,
      IsCompact K ∧ tsupport χ ⊆ K ∧ K ⊆ V ∧ 0 ≤ C ∧
      ∀ (Z E : ℝ) {ψ : SpinSpace 2}, hamiltonianGraph 2 Z ψ ((E : ℂ) • ψ) →
        ∃ u : SpinConfiguration 2 → Configuration 2 → ℂ,
          (∀ σ, LocallyLipschitz (u σ)) ∧
          (∀ᵐ x ∂volume, ∀ σ, ψ σ x = u σ x) ∧
          (∀ π : Equiv.Perm (Fin 2), ∀ σ, ∀ x,
            u (permuteSpin π σ) (permuteSpace π x) = permutationSign π • u σ x) ∧
          ∀ σ : SpinConfiguration 2,
            ∃ U : Lp ℂ 2 (volume : Measure (NuclearKSSpace (0 : Fin 2))),
            ∃ d : SpectatorCoordinate (0 : Fin 2) →
              Lp ℂ 2 (volume : Measure (NuclearKSSpace (0 : Fin 2))),
              U =ᵐ[volume] (fun p => χouter p • u σ (nuclearKSLift (0 : Fin 2) p)) ∧
              (∀ j, WeakProductL2Directional U (d j) (tDir j)) ∧
              ∀ j : SpectatorCoordinate (0 : Fin 2),
                let F : ℝ := ∫ p in K, ‖d j p‖ ^ 2
                let M : ℝ := ∫ p in K,
                  ‖-(fderiv ℝ (nuclearKSPotential (0 : Fin 2) Z E) p (tDir j) • U p) -
                    nuclearKSPotential (0 : Fin 2) Z E p • d j p‖ ^ 2
                M ≤ 2 * ((8 / 9 : ℝ) * |Z| + 128 / 121) ^ 2 *
                  (∫ p in K, ‖U p‖ ^ 2) +
                  2 * ((26 / 3 : ℝ) * |Z| + 8 / 11 + |E| / 2) ^ 2 * F ∧
                ∃ W : Lp ℂ 2 (volume : Measure (NuclearKSSpace (0 : Fin 2))),
                ∃ gy : Fin 4 → Lp ℂ 2 (volume : Measure (NuclearKSSpace (0 : Fin 2))),
                ∃ gt : SpectatorCoordinate (0 : Fin 2) →
                  Lp ℂ 2 (volume : Measure (NuclearKSSpace (0 : Fin 2))),
                ∃ hyy : Fin 4 → Fin 4 →
                  Lp ℂ 2 (volume : Measure (NuclearKSSpace (0 : Fin 2))),
                  W =ᵐ[volume] (fun p => χ p • d j p) ∧
                  (∑ i, ‖gy i‖ ^ 2) ≤ 2 * (C * F) + (3 / 4 : ℝ) * (C * (F + M)) ∧
                  (∑ k, ‖gt k‖ ^ 2) ≤ (C * (F + M)) / 64 ∧
                  (∑ i, ∑ k, ‖hyy i k‖ ^ 2) ≤ (3 / 2 : ℝ) * (C * (F + M)) ∧
                  (∀ i, WeakProductL2Directional W (gy i) (yDir i)) ∧
                  (∀ k, WeakProductL2Directional W (gt k) (tDir k)) ∧
                  ∀ i k, WeakProductL2Directional (gy i) (hyy i k) (yDir k) := by
  obtain ⟨χouter, houter, hcouter, hsouter, V, hV, hχV, hVO, houter1⟩ :=
    exists_outer_plateau hcχ (nuclearChartOpen_isOpen t0) hχΩ
  obtain ⟨K0, C0, hK0, houterK0, hK0Ω, hC0, hinit⟩ :=
    two_electron_nuclear_chart_initialization t0 ht0 houter hcouter hsouter
  obtain ⟨K, C, hK, hχK, hKV, hC, hgain⟩ :=
    local_weak_grushin_spectator_cutoff_gain (κ := SpectatorCoordinate (0 : Fin 2))
      (by norm_num : (0 : ℝ) < 4) hV hχ hcχ hχV
  refine ⟨χouter, houter, hcouter, hsouter, V, hV, hχV, hVO, houter1,
    K, C, hK, hχK, hKV, hC, ?_⟩
  intro Z E ψ hgraph
  obtain ⟨u, hu, hue, hperm, hbound, huinit⟩ := hinit Z E hgraph
  refine ⟨u, hu, hue, hperm, ?_⟩
  intro σ
  obtain ⟨U, gy0, d, hyy0, hU, hY0, hT0, hYY0, hgy0, hd, hhyy0⟩ := huinit σ
  refine ⟨U, d, hU, hd, ?_⟩
  intro j
  have he : (ψ σ : Configuration 2 → ℂ) =ᵐ[volume] u σ := by
    filter_upwards [hue] with x hx
    exact hx σ
  have hP := scalar_nuclear_output_on_plateau (0 : Fin 2) Z E (hgraph.2.2 σ)
    (hu σ).continuous he hU hVO (nuclearChartOpen_subset_coefficientPatch t0 ht0) houter1
  have hB : ContDiffOn ℝ ∞ (nuclearKSPotential (0 : Fin 2) Z E) V := by
    intro p hp
    exact (nuclearKSPotential_contDiffAt (0 : Fin 2) Z E
      (nuclearChartOpen_subset_coefficientPatch t0 ht0 (hVO hp))).contDiffWithinAt
  have hh := hgain (nuclearKSPotential (0 : Fin 2) Z E) U (d j) j hB (hd j) hP
  refine ⟨nuclear_chart_spectator_forcing_integral_le Z E t0 ht0 hK
    (hKV.trans hVO) U (d j) j, ?_⟩
  simpa only [show (16 : ℝ) * 4 = 64 by norm_num] using hh

#print axioms two_electron_nuclear_chart_spectator_bootstrap
end ManyBody.S8