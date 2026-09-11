import LocalWeakGrushinPotentialGain_v1
import ProductContinuousLocalL2_v1
import CoulombNuclearKSWeak_v1
import NuclearKSPotentialAnalytic_v1

/-! The actual weak Grushin gain applied to physical nuclear KS pullbacks.
The input is the actual scalar Coulomb graph and its continuous representative.
The exact coefficient patch admits the selected nuclear collision and excludes
the other nuclear and pair collisions; no enlargement of that domain is made. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace TheoremT.Continuum

theorem scalar_coulomb_nuclear_KS_one_step {N : ℕ} (i : Fin N) (Z E : ℝ)
    {χ : NuclearKSSpace i → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχΩ : tsupport χ ⊆ nuclearKSCoefficientPatch i) :
    ∃ K : Set (NuclearKSSpace i), ∃ C : ℝ,
      IsCompact K ∧ tsupport χ ⊆ K ∧ K ⊆ nuclearKSCoefficientPatch i ∧ 0 ≤ C ∧
      ∀ {f : SpatialL2 N}, scalarHamiltonianGraph N Z f ((E : ℂ) • f) →
      ∀ {g : Configuration N → ℂ}, Continuous g → ((f : Configuration N → ℂ) =ᵐ[volume] g) →
        let F : ℝ := ∫ p in K, ‖g (nuclearKSLift i p)‖^2
        let M : ℝ := ∫ p in K, ‖nuclearKSPotential i Z E p • g (nuclearKSLift i p)‖^2
        ∃ U : Lp ℂ 2 (volume : Measure (NuclearKSSpace i)),
        ∃ gy : Fin 4 → Lp ℂ 2 (volume : Measure (NuclearKSSpace i)),
        ∃ gt : SpectatorCoordinate i → Lp ℂ 2 (volume : Measure (NuclearKSSpace i)),
        ∃ hyy : Fin 4 → Fin 4 → Lp ℂ 2 (volume : Measure (NuclearKSSpace i)),
          U =ᵐ[volume] (fun p => χ p • g (nuclearKSLift i p)) ∧
          (∑ j, ‖gy j‖^2) ≤ 2*(C*F)+(3/4 : ℝ)*(C*(F+M)) ∧
          (∑ j, ‖gt j‖^2) ≤ (C*(F+M))/64 ∧
          (∑ j, ∑ k, ‖hyy j k‖^2) ≤ (3/2 : ℝ)*(C*(F+M)) ∧
          (∀ j, WeakProductL2Directional U (gy j) (WeakGrushin.yDir j)) ∧
          (∀ j, WeakProductL2Directional U (gt j) (WeakGrushin.tDir j)) ∧
          ∀ j k, WeakProductL2Directional (gy j) (hyy j k) (WeakGrushin.yDir k) := by
  obtain ⟨K,C,hK,hχK,hKΩ,hC,hgain⟩ :=
    WeakGrushin.local_weak_grushin_potential_cutoff_gain (κ := SpectatorCoordinate i)
      (by norm_num : (0 : ℝ) < 4) (nuclearKSCoefficientPatch_isOpen i) hχ hcχ hχΩ
  refine ⟨K,C,hK,hχK,hKΩ,hC,?_⟩
  intro f hgraph g hg hfg
  have hcont : Continuous (g ∘ nuclearKSLift i) := hg.comp (nuclearKSLift_contDiff i).continuous
  have hlocal : ProductLocallyL2On (g ∘ nuclearKSLift i) (nuclearKSCoefficientPatch i) :=
    product_continuousOn_locallyL2 hcont.continuousOn
  have hzero : ProductLocallyL2On (fun _ : NuclearKSSpace i => (0 : ℂ)) (nuclearKSCoefficientPatch i) :=
    product_continuousOn_locallyL2 continuous_const.continuousOn
  have hB : ContinuousOn (nuclearKSPotential i Z E) (nuclearKSCoefficientPatch i) := by
    intro q hq
    exact (nuclearKSPotential_contDiffAt_omega i Z E hq).continuousAt.continuousWithinAt
  have hBasis : (spectatorBasis : SpectatorCoordinate i → SpectatorConfiguration i) = oscillatorBasis := by
    funext j
    simp only [spectatorBasis,oscillatorBasis,EuclideanSpace.single,PiLp.single]
  have hP : ∀ φ : NuclearKSSpace i → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ nuclearKSCoefficientPatch i →
      (∫ p, splitGrushin 4 oscillatorBasis (nuclearKSPotential i Z E) φ p •
        (g ∘ nuclearKSLift i) p) = ∫ p, φ p • (0 : ℂ) := by
    intro φ hφ hcφ hsφ
    have hh := (scalar_coulomb_nuclear_KS_weak i hgraph hg hfg hφ hcφ hsφ).2
    rw [hBasis] at hh
    simpa only [Complex.real_smul,smul_zero,integral_zero] using hh
  have hh := hgain (nuclearKSPotential i Z E) (g ∘ nuclearKSLift i) (fun _ => 0)
    hB hlocal hzero hP
  simpa only [Function.comp_apply,zero_sub,norm_neg,show (16 : ℝ)*4=64 by norm_num] using hh

#print axioms scalar_coulomb_nuclear_KS_one_step
end TheoremT.Continuum
