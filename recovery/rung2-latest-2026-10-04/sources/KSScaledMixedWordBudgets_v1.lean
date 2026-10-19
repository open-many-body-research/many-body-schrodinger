import KSScaledFiniteCoefficientBounds_v1
import MixedWordFDeriv_v1
import SmoothMixedSourceWords_v1

/-! Actual uniform mixed Y/T coefficient and source words for physical KS
charts. A single finite-order constant precedes epsilon, amplitude and region.
All required source weak links and integral budgets are derived. The operator
uses epsilon*b_epsilon, while the source uses b_epsilon smul (-a0). -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum
open WeakGrushin

theorem nuclearKS_uniform_mixed_word_data {N : ℕ} (i : Fin N)
    (Z E : ℝ)
    {K : Set (NuclearKSSpace i)} (hK : IsCompact K) (hKpatch : K ⊆ nuclearKSCoefficientPatch i) (m : ℕ) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
      (∀ (a : List (Fin 4)) (t : List (SpectatorCoordinate i)), a.length+t.length ≤ m → ∀ q ∈ K,
        |directionalWordDeriv yDir (spectatorWordDeriv (nuclearKSPotential i Z (ε*E)) t) a q| ≤ M ∧
        |directionalWordDeriv yDir (spectatorWordDeriv (epsilonNuclearKSPotential i ε Z E) t) a q| ≤ M) ∧
      ∀ a0 : ℂ,
        (∀ (a : List (Fin 4)) (t : List (SpectatorCoordinate i)),
          ProductLocallyL2On (fun p => directionalWordDeriv yDir (spectatorWordDeriv (nuclearKSPotential i Z (ε*E)) t) a p • (-a0)) (nuclearKSCoefficientPatch i)) ∧
        (∀ (a : List (Fin 4)) (t : List (SpectatorCoordinate i)) (jY : Fin 4),
          ProductLocalWeakDirectional (nuclearKSCoefficientPatch i)
            (fun p => directionalWordDeriv yDir (spectatorWordDeriv (nuclearKSPotential i Z (ε*E)) t) a p • (-a0))
            (fun p => directionalWordDeriv yDir (spectatorWordDeriv (nuclearKSPotential i Z (ε*E)) t) (jY::a) p • (-a0)) (yDir jY)) ∧
        (∀ (t : List (SpectatorCoordinate i)) (j : SpectatorCoordinate i),
          ProductLocalWeakDirectional (nuclearKSCoefficientPatch i)
            (fun p => directionalWordDeriv yDir (spectatorWordDeriv (nuclearKSPotential i Z (ε*E)) t) [] p • (-a0))
            (fun p => directionalWordDeriv yDir (spectatorWordDeriv (nuclearKSPotential i Z (ε*E)) (j::t)) [] p • (-a0)) (tDir j)) ∧
        ∀ S : Set (NuclearKSSpace i), MeasurableSet S → S ⊆ K →
          ∀ (a : List (Fin 4)) (t : List (SpectatorCoordinate i)), a.length+t.length ≤ m →
            RegionL2Budget (fun p => directionalWordDeriv yDir (spectatorWordDeriv (nuclearKSPotential i Z (ε*E)) t) a p • (-a0)) S (M^2*‖a0‖^2*(volume S).toReal) := by
  obtain ⟨M,hM,hbounds⟩ := nuclearKS_uniform_finite_scaled_jets i Z E hK hKpatch m
  refine ⟨M,hM,?_⟩
  intro ε hε hε1
  have hb : ContDiffOn ℝ ∞ (nuclearKSPotential i Z (ε*E)) (nuclearKSCoefficientPatch i) := by
    intro p hp
    exact (nuclearKSPotential_contDiffAt i Z (ε*E) hp).contDiffWithinAt
  have hs : ContDiffOn ℝ ∞ (epsilonNuclearKSPotential i ε Z E) (nuclearKSCoefficientPatch i) := by
    intro p hp
    exact (epsilonNuclearKSPotential_contDiffAt i ε Z E hp).contDiffWithinAt
  have hw (a : List (Fin 4)) (t : List (SpectatorCoordinate i)) (hat : a.length+t.length ≤ m)
      (p : NuclearKSSpace i) (hp : p ∈ K) :
      |directionalWordDeriv yDir (spectatorWordDeriv (nuclearKSPotential i Z (ε*E)) t) a p| ≤ M ∧
      |directionalWordDeriv yDir (spectatorWordDeriv (epsilonNuclearKSPotential i ε Z E) t) a p| ≤ M := by
    obtain ⟨hbare,hscaled,_⟩ := hbounds ε hε hε1 (a.length+t.length) hat p hp
    exact ⟨(mixedWordDeriv_abs_le_iteratedFDeriv (nuclearKSCoefficientPatch_isOpen i) hb a t (hKpatch hp)).trans hbare,
      (mixedWordDeriv_abs_le_iteratedFDeriv (nuclearKSCoefficientPatch_isOpen i) hs a t (hKpatch hp)).trans hscaled⟩
  refine ⟨hw,?_⟩
  intro a0
  obtain ⟨hlocal,hY,hT⟩ := smooth_mixed_source_words (nuclearKSCoefficientPatch_isOpen i) hb (-a0)
  refine ⟨hlocal,hY,hT,?_⟩
  intro S hS hSK a t hat
  have hfinite : volume S < ⊤ := (measure_mono hSK).trans_lt hK.measure_lt_top
  simpa only [norm_neg] using smooth_mixed_source_region_budget (nuclearKSCoefficientPatch_isOpen i) hb (-a0) a t hS
    (hSK.trans hKpatch) hfinite (le_trans (by norm_num) hM)
    (fun p hp => (hw a t hat p (hSK hp)).1)

theorem pairKS_uniform_mixed_word_data (Z E : ℝ)
    {K : Set (PairKSSpace)} (hK : IsCompact K) (hKpatch : K ⊆ pairKSCoefficientPatch) (m : ℕ) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
      (∀ (a : List (Fin 4)) (t : List (SpectatorCoordinate (0 : Fin 2))), a.length+t.length ≤ m → ∀ q ∈ K,
        |directionalWordDeriv yDir (spectatorWordDeriv (pairKSPotential Z (ε*E)) t) a q| ≤ M ∧
        |directionalWordDeriv yDir (spectatorWordDeriv (epsilonPairKSPotential ε Z E) t) a q| ≤ M) ∧
      ∀ a0 : ℂ,
        (∀ (a : List (Fin 4)) (t : List (SpectatorCoordinate (0 : Fin 2))),
          ProductLocallyL2On (fun p => directionalWordDeriv yDir (spectatorWordDeriv (pairKSPotential Z (ε*E)) t) a p • (-a0)) (pairKSCoefficientPatch)) ∧
        (∀ (a : List (Fin 4)) (t : List (SpectatorCoordinate (0 : Fin 2))) (jY : Fin 4),
          ProductLocalWeakDirectional (pairKSCoefficientPatch)
            (fun p => directionalWordDeriv yDir (spectatorWordDeriv (pairKSPotential Z (ε*E)) t) a p • (-a0))
            (fun p => directionalWordDeriv yDir (spectatorWordDeriv (pairKSPotential Z (ε*E)) t) (jY::a) p • (-a0)) (yDir jY)) ∧
        (∀ (t : List (SpectatorCoordinate (0 : Fin 2))) (j : SpectatorCoordinate (0 : Fin 2)),
          ProductLocalWeakDirectional (pairKSCoefficientPatch)
            (fun p => directionalWordDeriv yDir (spectatorWordDeriv (pairKSPotential Z (ε*E)) t) [] p • (-a0))
            (fun p => directionalWordDeriv yDir (spectatorWordDeriv (pairKSPotential Z (ε*E)) (j::t)) [] p • (-a0)) (tDir j)) ∧
        ∀ S : Set (PairKSSpace), MeasurableSet S → S ⊆ K →
          ∀ (a : List (Fin 4)) (t : List (SpectatorCoordinate (0 : Fin 2))), a.length+t.length ≤ m →
            RegionL2Budget (fun p => directionalWordDeriv yDir (spectatorWordDeriv (pairKSPotential Z (ε*E)) t) a p • (-a0)) S (M^2*‖a0‖^2*(volume S).toReal) := by
  obtain ⟨M,hM,hbounds⟩ := pairKS_uniform_finite_scaled_jets Z E hK hKpatch m
  refine ⟨M,hM,?_⟩
  intro ε hε hε1
  have hb : ContDiffOn ℝ ∞ (pairKSPotential Z (ε*E)) (pairKSCoefficientPatch) := by
    intro p hp
    exact (pairKSPotential_contDiffAt Z (ε*E) hp).contDiffWithinAt
  have hs : ContDiffOn ℝ ∞ (epsilonPairKSPotential ε Z E) (pairKSCoefficientPatch) := by
    intro p hp
    exact (epsilonPairKSPotential_contDiffAt ε Z E hp).contDiffWithinAt
  have hw (a : List (Fin 4)) (t : List (SpectatorCoordinate (0 : Fin 2))) (hat : a.length+t.length ≤ m)
      (p : PairKSSpace) (hp : p ∈ K) :
      |directionalWordDeriv yDir (spectatorWordDeriv (pairKSPotential Z (ε*E)) t) a p| ≤ M ∧
      |directionalWordDeriv yDir (spectatorWordDeriv (epsilonPairKSPotential ε Z E) t) a p| ≤ M := by
    obtain ⟨hbare,hscaled,_⟩ := hbounds ε hε hε1 (a.length+t.length) hat p hp
    exact ⟨(mixedWordDeriv_abs_le_iteratedFDeriv pairKSCoefficientPatch_isOpen hb a t (hKpatch hp)).trans hbare,
      (mixedWordDeriv_abs_le_iteratedFDeriv pairKSCoefficientPatch_isOpen hs a t (hKpatch hp)).trans hscaled⟩
  refine ⟨hw,?_⟩
  intro a0
  obtain ⟨hlocal,hY,hT⟩ := smooth_mixed_source_words pairKSCoefficientPatch_isOpen hb (-a0)
  refine ⟨hlocal,hY,hT,?_⟩
  intro S hS hSK a t hat
  have hfinite : volume S < ⊤ := (measure_mono hSK).trans_lt hK.measure_lt_top
  simpa only [norm_neg] using smooth_mixed_source_region_budget pairKSCoefficientPatch_isOpen hb (-a0) a t hS
    (hSK.trans hKpatch) hfinite (le_trans (by norm_num) hM)
    (fun p hp => (hw a t hat p (hSK hp)).1)

#print axioms nuclearKS_uniform_mixed_word_data
#print axioms pairKS_uniform_mixed_word_data
end TheoremT.Continuum
