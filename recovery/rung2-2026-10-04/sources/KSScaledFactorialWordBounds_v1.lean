import KSScaledFactorialCoefficientBounds_v1
import KSScaledMixedWordBudgets_v1

/-! Every mixed coordinate word of the actual physical coefficient and forcing
has the same factorial majorant. Region budgets use the actual restricted
Lebesgue measure and squared L2 norm. There is no finite-order parameter m.
Weak source derivative identities are supplied by smooth_mixed_source_words;
these norm estimates do not assert solution analyticity. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum
open WeakGrushin

theorem nuclearKS_uniform_factorial_word_bounds {N : ℕ} (i : Fin N) (Z E : ℝ)
    {K : Set (NuclearKSSpace i)} (hK : IsCompact K)
    (hKpatch : K ⊆ nuclearKSCoefficientPatch i) :
    ∃ C A : ℝ, 1 ≤ C ∧ 1 ≤ A ∧ ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
      ∀ (a : List (Fin 4)) (t : List (SpectatorCoordinate i)),
        (∀ q ∈ K,
          |directionalWordDeriv yDir (spectatorWordDeriv (nuclearKSPotential i Z (ε*E)) t) a q| ≤
            C*A^(a.length+t.length)*((a.length+t.length).factorial : ℝ) ∧
          |directionalWordDeriv yDir (spectatorWordDeriv (epsilonNuclearKSPotential i ε Z E) t) a q| ≤
            ε*(C*A^(a.length+t.length)*((a.length+t.length).factorial : ℝ))) ∧
        ∀ a0 : ℂ, ∀ S : Set (NuclearKSSpace i), MeasurableSet S → S ⊆ K →
          RegionL2Budget
            (fun p => directionalWordDeriv yDir
              (spectatorWordDeriv (nuclearKSPotential i Z (ε*E)) t) a p • (-a0)) S
            ((C*A^(a.length+t.length)*((a.length+t.length).factorial : ℝ))^2 *
              ‖a0‖^2 * (volume S).toReal) := by
  obtain ⟨C,A,hC,hA,hbounds⟩ := nuclearKS_uniform_factorial_scaled_jets i Z E hK hKpatch
  have hCp : 0 ≤ C := by linarith
  have hAp : 0 ≤ A := by linarith
  refine ⟨C,A,hC,hA,?_⟩
  intro ε hε hε1 a t
  have hb : ContDiffOn ℝ ∞ (nuclearKSPotential i Z (ε*E)) (nuclearKSCoefficientPatch i) := by
    intro p hp
    exact (nuclearKSPotential_contDiffAt i Z (ε*E) hp).contDiffWithinAt
  have hs : ContDiffOn ℝ ∞ (epsilonNuclearKSPotential i ε Z E) (nuclearKSCoefficientPatch i) := by
    intro p hp
    exact (epsilonNuclearKSPotential_contDiffAt i ε Z E hp).contDiffWithinAt
  have hw (p : NuclearKSSpace i) (hp : p ∈ K) :=
    hbounds ε hε hε1 (a.length+t.length) p hp
  have hword (p : NuclearKSSpace i) (hp : p ∈ K) :
      |directionalWordDeriv yDir (spectatorWordDeriv (nuclearKSPotential i Z (ε*E)) t) a p| ≤
        C*A^(a.length+t.length)*((a.length+t.length).factorial : ℝ) :=
    (mixedWordDeriv_abs_le_iteratedFDeriv (nuclearKSCoefficientPatch_isOpen i) hb a t
      (hKpatch hp)).trans (hw p hp).1
  refine ⟨fun p hp => ⟨hword p hp,?_,⟩,?_⟩
  · exact (mixedWordDeriv_abs_le_iteratedFDeriv (nuclearKSCoefficientPatch_isOpen i) hs a t
      (hKpatch hp)).trans (hw p hp).2.1
  · intro a0 S hS hSK
    have hfinite : volume S < ⊤ := (measure_mono hSK).trans_lt hK.measure_lt_top
    simpa only [norm_neg] using smooth_mixed_source_region_budget
      (nuclearKSCoefficientPatch_isOpen i) hb (-a0) a t hS (hSK.trans hKpatch) hfinite
      (show 0 ≤ C*A^(a.length+t.length)*((a.length+t.length).factorial : ℝ) from by positivity)
      (fun p hp => hword p (hSK hp))

theorem pairKS_uniform_factorial_word_bounds (Z E : ℝ)
    {K : Set PairKSSpace} (hK : IsCompact K) (hKpatch : K ⊆ pairKSCoefficientPatch) :
    ∃ C A : ℝ, 1 ≤ C ∧ 1 ≤ A ∧ ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
      ∀ (a : List (Fin 4)) (t : List (SpectatorCoordinate (0 : Fin 2))),
        (∀ q ∈ K,
          |directionalWordDeriv yDir (spectatorWordDeriv (pairKSPotential Z (ε*E)) t) a q| ≤
            C*A^(a.length+t.length)*((a.length+t.length).factorial : ℝ) ∧
          |directionalWordDeriv yDir (spectatorWordDeriv (epsilonPairKSPotential ε Z E) t) a q| ≤
            ε*(C*A^(a.length+t.length)*((a.length+t.length).factorial : ℝ))) ∧
        ∀ a0 : ℂ, ∀ S : Set PairKSSpace, MeasurableSet S → S ⊆ K →
          RegionL2Budget
            (fun p => directionalWordDeriv yDir
              (spectatorWordDeriv (pairKSPotential Z (ε*E)) t) a p • (-a0)) S
            ((C*A^(a.length+t.length)*((a.length+t.length).factorial : ℝ))^2 *
              ‖a0‖^2 * (volume S).toReal) := by
  obtain ⟨C,A,hC,hA,hbounds⟩ := pairKS_uniform_factorial_scaled_jets Z E hK hKpatch
  have hCp : 0 ≤ C := by linarith
  have hAp : 0 ≤ A := by linarith
  refine ⟨C,A,hC,hA,?_⟩
  intro ε hε hε1 a t
  have hb : ContDiffOn ℝ ∞ (pairKSPotential Z (ε*E)) pairKSCoefficientPatch := by
    intro p hp
    exact (pairKSPotential_contDiffAt Z (ε*E) hp).contDiffWithinAt
  have hs : ContDiffOn ℝ ∞ (epsilonPairKSPotential ε Z E) pairKSCoefficientPatch := by
    intro p hp
    exact (epsilonPairKSPotential_contDiffAt ε Z E hp).contDiffWithinAt
  have hw (p : PairKSSpace) (hp : p ∈ K) := hbounds ε hε hε1 (a.length+t.length) p hp
  have hword (p : PairKSSpace) (hp : p ∈ K) :
      |directionalWordDeriv yDir (spectatorWordDeriv (pairKSPotential Z (ε*E)) t) a p| ≤
        C*A^(a.length+t.length)*((a.length+t.length).factorial : ℝ) :=
    (mixedWordDeriv_abs_le_iteratedFDeriv pairKSCoefficientPatch_isOpen hb a t
      (hKpatch hp)).trans (hw p hp).1
  refine ⟨fun p hp => ⟨hword p hp,?_,⟩,?_⟩
  · exact (mixedWordDeriv_abs_le_iteratedFDeriv pairKSCoefficientPatch_isOpen hs a t
      (hKpatch hp)).trans (hw p hp).2.1
  · intro a0 S hS hSK
    have hfinite : volume S < ⊤ := (measure_mono hSK).trans_lt hK.measure_lt_top
    simpa only [norm_neg] using smooth_mixed_source_region_budget
      pairKSCoefficientPatch_isOpen hb (-a0) a t hS (hSK.trans hKpatch) hfinite
      (show 0 ≤ C*A^(a.length+t.length)*((a.length+t.length).factorial : ℝ) from by positivity)
      (fun p hp => hword p (hSK hp))

end TheoremT.Continuum
