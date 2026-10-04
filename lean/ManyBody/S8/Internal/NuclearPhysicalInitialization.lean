import ManyBody.S8.HomogeneousGrushinOneStep
import CoulombNuclearKSOneStep_v1

/-! The bounded-potential gain on a subset of the actual nuclear coefficient patch.
The only solution input is the physical scalar Coulomb eigenfunction graph and
its continuous representative. The transformed equation is proved from that graph.
-/
noncomputable section
open MeasureTheory
open scoped Topology ContDiff BigOperators
open TheoremT.Continuum TheoremT.Continuum.WeakGrushin

namespace ManyBody.S8

theorem scalar_nuclear_bounded_cutoff_gain {N : ℕ} (i : Fin N)
    {Ω : Set (NuclearKSSpace i)} (hΩ : IsOpen Ω)
    (hΩpatch : Ω ⊆ nuclearKSCoefficientPatch i)
    {χ : NuclearKSSpace i → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχΩ : tsupport χ ⊆ Ω) :
    ∃ K : Set (NuclearKSSpace i), ∃ C : ℝ,
      IsCompact K ∧ tsupport χ ⊆ K ∧ K ⊆ Ω ∧ 0 ≤ C ∧
      ∀ (Z E : ℝ) {f : SpatialL2 N}, scalarHamiltonianGraph N Z f ((E : ℂ) • f) →
      ∀ {g : Configuration N → ℂ}, Continuous g →
        ((f : Configuration N → ℂ) =ᵐ[volume] g) →
      ∀ (b : ℝ), 0 ≤ b → (∀ p ∈ K, ‖nuclearKSPotential i Z E p‖ ≤ b) →
        let F : ℝ := ∫ p in K, ‖g (nuclearKSLift i p)‖ ^ 2
        ∃ U : Lp ℂ 2 (volume : Measure (NuclearKSSpace i)),
        ∃ gy : Fin 4 → Lp ℂ 2 (volume : Measure (NuclearKSSpace i)),
        ∃ gt : SpectatorCoordinate i → Lp ℂ 2 (volume : Measure (NuclearKSSpace i)),
        ∃ hyy : Fin 4 → Fin 4 → Lp ℂ 2 (volume : Measure (NuclearKSSpace i)),
          U =ᵐ[volume] (fun p => χ p • g (nuclearKSLift i p)) ∧
          (∑ j, ‖gy j‖ ^ 2) ≤ C * (11 / 4 + 3 / 4 * b ^ 2) * F ∧
          (∑ j, ‖gt j‖ ^ 2) ≤ (C * (1 + b ^ 2) * F) / 64 ∧
          (∑ j, ∑ k, ‖hyy j k‖ ^ 2) ≤ 3 / 2 * C * (1 + b ^ 2) * F ∧
          (∀ j, WeakProductL2Directional U (gy j) (yDir j)) ∧
          (∀ j, WeakProductL2Directional U (gt j) (tDir j)) ∧
          ∀ j k, WeakProductL2Directional (gy j) (hyy j k) (yDir k) := by
  obtain ⟨K, C, hK, hχK, hKΩ, hC, hgain⟩ :=
    local_weak_grushin_homogeneous_cutoff_gain (κ := SpectatorCoordinate i)
      (by norm_num : (0 : ℝ) < 4) hΩ hχ hcχ hχΩ
  refine ⟨K, C, hK, hχK, hKΩ, hC, ?_⟩
  intro Z E f hgraph g hg hfg b hb hBb
  have hcont : Continuous (g ∘ nuclearKSLift i) :=
    hg.comp (nuclearKSLift_contDiff i).continuous
  have hlocal : ProductLocallyL2On (g ∘ nuclearKSLift i) Ω :=
    product_continuousOn_locallyL2 hcont.continuousOn
  have hB : ContinuousOn (nuclearKSPotential i Z E) Ω := by
    intro q hq
    exact (nuclearKSPotential_contDiffAt_omega i Z E (hΩpatch hq)).continuousAt.continuousWithinAt
  have hBasis : (spectatorBasis : SpectatorCoordinate i → SpectatorConfiguration i) =
      oscillatorBasis := by
    funext j
    simp only [spectatorBasis, oscillatorBasis, EuclideanSpace.single, PiLp.single]
  have hP : ∀ φ : NuclearKSSpace i → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ω →
      (∫ p, splitGrushin 4 oscillatorBasis (nuclearKSPotential i Z E) φ p •
        (g ∘ nuclearKSLift i) p) = 0 := by
    intro φ hφ hcφ hsφ
    have hh := (scalar_coulomb_nuclear_KS_weak i hgraph hg hfg hφ hcφ
      (hsφ.trans hΩpatch)).2
    rw [hBasis] at hh
    simpa only [Complex.real_smul] using hh
  have hh := hgain b (nuclearKSPotential i Z E) (g ∘ nuclearKSLift i)
    hb hB hlocal hBb hP
  simpa only [Function.comp_apply, show (16 : ℝ) * 4 = 64 by norm_num] using hh

#print axioms scalar_nuclear_bounded_cutoff_gain
end ManyBody.S8