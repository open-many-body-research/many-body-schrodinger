import AnalyticAffineCompactFactorialJets_v1
import KSPotentialEnergyAffine_v1
import NuclearKSPotentialAnalytic_v1
import PairKSPotentialAnalytic_v1

/-! Actual physical KS coefficient and normalized forcing bounds at every order.
For each compact subset of the genuine coefficient patch, two constants work
simultaneously for every scale in [0,1], point, and derivative order.
The scaled potential is small by epsilon; the normalized forcing has no inverse
epsilon. No solution regularity or quantitative computation of C,A is asserted. -/
noncomputable section
open scoped ContDiff
namespace TheoremT.Continuum

theorem nuclearKS_energy_coefficient_analyticAt {N : ℕ} (i : Fin N) (E : ℝ)
    (q : NuclearKSSpace i) :
    AnalyticAt ℝ (fun p : NuclearKSSpace i => -8*E*‖p.1‖^2) q := by
  have h : ContDiff ℝ ω (fun p : NuclearKSSpace i => ‖p.1‖^2) :=
    (contDiff_norm_sq ℝ).comp contDiff_fst
  exact (contDiff_const.mul h).contDiffAt.analyticAt

theorem pairKS_energy_coefficient_analyticAt (E : ℝ) (q : PairKSSpace) :
    AnalyticAt ℝ (fun p : PairKSSpace => -4*E*‖p.1‖^2) q := by
  have h : ContDiff ℝ ω (fun p : PairKSSpace => ‖p.1‖^2) :=
    (contDiff_norm_sq ℝ).comp contDiff_fst
  exact (contDiff_const.mul h).contDiffAt.analyticAt

theorem nuclearKS_uniform_factorial_scaled_jets {N : ℕ} (i : Fin N)
    (Z E : ℝ) {K : Set (NuclearKSSpace i)} (hK : IsCompact K)
    (hKpatch : K ⊆ nuclearKSCoefficientPatch i) :
    ∃ C A : ℝ, 1 ≤ C ∧ 1 ≤ A ∧
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ k : ℕ, ∀ q ∈ K,
        ‖iteratedFDeriv ℝ k (nuclearKSPotential i Z (ε*E)) q‖ ≤
          C * A^k * (k.factorial : ℝ) ∧
        ‖iteratedFDeriv ℝ k (epsilonNuclearKSPotential i ε Z E) q‖ ≤
          ε * (C * A^k * (k.factorial : ℝ)) ∧
        ∀ a0 : ℂ,
          ‖iteratedFDeriv ℝ k (fun p => nuclearKSPotential i Z (ε*E) p • (-a0)) q‖ ≤
            (C * A^k * (k.factorial : ℝ)) * ‖a0‖ := by
  have h0 : AnalyticOnNhd ℝ (nuclearKSPotential i Z 0) K :=
    fun q hq => nuclearKSPotential_analyticAt i Z 0 (hKpatch hq)
  have h1 : AnalyticOnNhd ℝ (fun p : NuclearKSSpace i => -8*E*‖p.1‖^2) K :=
    fun q _ => nuclearKS_energy_coefficient_analyticAt i E q
  obtain ⟨C,A,hC,hA,hbound⟩ := analytic_affine_compact_factorial_source_bound hK h0 h1
  refine ⟨C,A,hC,hA,?_⟩
  intro ε hε hε1 k q hq
  obtain ⟨hbare,hscaled,hsource⟩ := hbound ε hε hε1 k q hq
  refine ⟨?_,?_,?_⟩
  · simpa only [nuclearKSPotential_scaled_energy_affine_fun] using hbare
  · change ‖iteratedFDeriv ℝ k (fun p => ε * nuclearKSPotential i Z (ε*E) p) q‖ ≤ _
    simpa only [nuclearKSPotential_scaled_energy_affine_fun] using hscaled
  · intro a0
    simpa only [nuclearKSPotential_scaled_energy_affine_fun,norm_neg] using hsource (-a0)

theorem pairKS_uniform_factorial_scaled_jets
    (Z E : ℝ) {K : Set PairKSSpace} (hK : IsCompact K)
    (hKpatch : K ⊆ pairKSCoefficientPatch) :
    ∃ C A : ℝ, 1 ≤ C ∧ 1 ≤ A ∧
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ k : ℕ, ∀ q ∈ K,
        ‖iteratedFDeriv ℝ k (pairKSPotential Z (ε*E)) q‖ ≤
          C * A^k * (k.factorial : ℝ) ∧
        ‖iteratedFDeriv ℝ k (epsilonPairKSPotential ε Z E) q‖ ≤
          ε * (C * A^k * (k.factorial : ℝ)) ∧
        ∀ a0 : ℂ,
          ‖iteratedFDeriv ℝ k (fun p => pairKSPotential Z (ε*E) p • (-a0)) q‖ ≤
            (C * A^k * (k.factorial : ℝ)) * ‖a0‖ := by
  have h0 : AnalyticOnNhd ℝ (pairKSPotential Z 0) K :=
    fun q hq => pairKSPotential_analyticAt Z 0 (hKpatch hq)
  have h1 : AnalyticOnNhd ℝ (fun p : PairKSSpace => -4*E*‖p.1‖^2) K :=
    fun q _ => pairKS_energy_coefficient_analyticAt E q
  obtain ⟨C,A,hC,hA,hbound⟩ := analytic_affine_compact_factorial_source_bound hK h0 h1
  refine ⟨C,A,hC,hA,?_⟩
  intro ε hε hε1 k q hq
  obtain ⟨hbare,hscaled,hsource⟩ := hbound ε hε hε1 k q hq
  refine ⟨?_,?_,?_⟩
  · simpa only [pairKSPotential_scaled_energy_affine_fun] using hbare
  · change ‖iteratedFDeriv ℝ k (fun p => ε * pairKSPotential Z (ε*E) p) q‖ ≤ _
    simpa only [pairKSPotential_scaled_energy_affine_fun] using hscaled
  · intro a0
    simpa only [pairKSPotential_scaled_energy_affine_fun,norm_neg] using hsource (-a0)

end TheoremT.Continuum
