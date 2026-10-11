import SmoothAffineCompactFiniteJets_v1
import KSPotentialEnergyAffine_v1

/-! Scale-uniform finite coefficient and forcing jets for the actual physical
KS potentials. The bound depends on the fixed compact patch, Z, E and finite
reserve m. It is chosen before epsilon, derivative order and source amplitude.
No factorial dependence on m or executable evaluation of the bound is asserted.
The forcing b_epsilon smul (-a0) is the normalized-difference forcing. -/
noncomputable section
open scoped ContDiff
namespace TheoremT.Continuum

theorem nuclearKS_uniform_finite_scaled_jets {N : ℕ} (i : Fin N)
    (Z E : ℝ) {K : Set (NuclearKSSpace i)} (hK : IsCompact K)
    (hKpatch : K ⊆ nuclearKSCoefficientPatch i) (m : ℕ) :
    ∃ M : ℝ, 1 ≤ M ∧
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ k : ℕ, k ≤ m → ∀ q ∈ K,
        ‖iteratedFDeriv ℝ k (nuclearKSPotential i Z (ε*E)) q‖ ≤ M ∧
        ‖iteratedFDeriv ℝ k (epsilonNuclearKSPotential i ε Z E) q‖ ≤ M ∧
        ∀ a0 : ℂ,
          ‖iteratedFDeriv ℝ k (fun p => nuclearKSPotential i Z (ε*E) p • (-a0)) q‖ ≤
            M * ‖a0‖ := by
  have h0 : ContDiffOn ℝ ∞ (nuclearKSPotential i Z 0) (nuclearKSCoefficientPatch i) := by
    intro q hq
    exact (nuclearKSPotential_contDiffAt i Z 0 hq).contDiffWithinAt
  obtain ⟨M,hM,hbound⟩ := smooth_affine_compact_finite_source_bound
    (nuclearKSCoefficientPatch_isOpen i) hK hKpatch h0
    (nuclearKS_energy_coefficient_contDiff i E).contDiffOn m
  refine ⟨M,hM,?_⟩
  intro ε hε hε1 k hk q hq
  obtain ⟨hbare,hscaled,hsource⟩ := hbound ε hε hε1 k hk q hq
  refine ⟨?_,?_,?_⟩
  · simpa only [nuclearKSPotential_scaled_energy_affine_fun] using hbare
  · change ‖iteratedFDeriv ℝ k (fun p => ε * nuclearKSPotential i Z (ε*E) p) q‖ ≤ M
    simpa only [nuclearKSPotential_scaled_energy_affine_fun] using hscaled
  · intro a0
    simpa only [nuclearKSPotential_scaled_energy_affine_fun,norm_neg] using hsource (-a0)

theorem pairKS_uniform_finite_scaled_jets
    (Z E : ℝ) {K : Set PairKSSpace} (hK : IsCompact K)
    (hKpatch : K ⊆ pairKSCoefficientPatch) (m : ℕ) :
    ∃ M : ℝ, 1 ≤ M ∧
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ k : ℕ, k ≤ m → ∀ q ∈ K,
        ‖iteratedFDeriv ℝ k (pairKSPotential Z (ε*E)) q‖ ≤ M ∧
        ‖iteratedFDeriv ℝ k (epsilonPairKSPotential ε Z E) q‖ ≤ M ∧
        ∀ a0 : ℂ,
          ‖iteratedFDeriv ℝ k (fun p => pairKSPotential Z (ε*E) p • (-a0)) q‖ ≤
            M * ‖a0‖ := by
  have h0 : ContDiffOn ℝ ∞ (pairKSPotential Z 0) pairKSCoefficientPatch := by
    intro q hq
    exact (pairKSPotential_contDiffAt Z 0 hq).contDiffWithinAt
  obtain ⟨M,hM,hbound⟩ := smooth_affine_compact_finite_source_bound
    pairKSCoefficientPatch_isOpen hK hKpatch h0
    (pairKS_energy_coefficient_contDiff E).contDiffOn m
  refine ⟨M,hM,?_⟩
  intro ε hε hε1 k hk q hq
  obtain ⟨hbare,hscaled,hsource⟩ := hbound ε hε hε1 k hk q hq
  refine ⟨?_,?_,?_⟩
  · simpa only [pairKSPotential_scaled_energy_affine_fun] using hbare
  · change ‖iteratedFDeriv ℝ k (fun p => ε * pairKSPotential Z (ε*E) p) q‖ ≤ M
    simpa only [pairKSPotential_scaled_energy_affine_fun] using hscaled
  · intro a0
    simpa only [pairKSPotential_scaled_energy_affine_fun,norm_neg] using hsource (-a0)

#print axioms nuclearKS_uniform_finite_scaled_jets
#print axioms pairKS_uniform_finite_scaled_jets
end TheoremT.Continuum
