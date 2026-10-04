import KSScaledFiniteCoefficientBounds_v1
import SpectatorWordFDeriv_v1
import SpectatorSmoothSourceRegionBudget_v1

/-! Uniform actual ordered spectator coefficient and forcing data for the
physical nuclear and pair KS charts. M is chosen before epsilon, the word,
the amplitude and the integration region. Source words are genuine weak
T derivatives of b_epsilon smul (-a0), not supplied solution derivatives.
Only finite coefficient reserves are bounded; no factorial rate is claimed. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum
open WeakGrushin

theorem nuclearKS_uniform_spectator_word_data {N : ℕ} (i : Fin N)
    (Z E : ℝ)
    {K : Set (NuclearKSSpace i)} (hK : IsCompact K)
    (hKpatch : K ⊆ nuclearKSCoefficientPatch i) (m : ℕ) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
      (∀ w : List (SpectatorCoordinate i), w.length ≤ m → ∀ q ∈ K,
        |spectatorWordDeriv (nuclearKSPotential i Z (ε*E)) w q| ≤ M ∧
        |spectatorWordDeriv (epsilonNuclearKSPotential i ε Z E) w q| ≤ M) ∧
      ∀ a0 : ℂ,
        (∀ w : List (SpectatorCoordinate i), ProductLocallyL2On
          (fun p => spectatorWordDeriv (nuclearKSPotential i Z (ε*E)) w p • (-a0))
          (nuclearKSCoefficientPatch i)) ∧
        (∀ (w : List (SpectatorCoordinate i)) (j : SpectatorCoordinate i),
          LocalSpectatorD (nuclearKSCoefficientPatch i)
            (fun p => spectatorWordDeriv (nuclearKSPotential i Z (ε*E)) w p • (-a0))
            (fun p => spectatorWordDeriv (nuclearKSPotential i Z (ε*E)) (j::w) p • (-a0)) j) ∧
        ∀ (S : Set (NuclearKSSpace i)), MeasurableSet S → S ⊆ K →
          ∀ w : List (SpectatorCoordinate i), w.length ≤ m →
            RegionL2Budget
              (fun p => spectatorWordDeriv (nuclearKSPotential i Z (ε*E)) w p • (-a0)) S
              (M^2*‖a0‖^2*(volume S).toReal) := by
  obtain ⟨M,hM,hbounds⟩ := nuclearKS_uniform_finite_scaled_jets i Z E hK hKpatch m
  refine ⟨M,hM,?_⟩
  intro ε hε hε1
  have hb : ContDiffOn ℝ ∞ (nuclearKSPotential i Z (ε*E)) (nuclearKSCoefficientPatch i) := by
    intro q hq
    exact (nuclearKSPotential_contDiffAt i Z (ε*E) hq).contDiffWithinAt
  have hs : ContDiffOn ℝ ∞ (epsilonNuclearKSPotential i ε Z E) (nuclearKSCoefficientPatch i) := by
    intro q hq
    exact (epsilonNuclearKSPotential_contDiffAt i ε Z E hq).contDiffWithinAt
  have hw (w : List (SpectatorCoordinate i)) (hw : w.length ≤ m) (q : NuclearKSSpace i)
      (hq : q ∈ K) :
      |spectatorWordDeriv (nuclearKSPotential i Z (ε*E)) w q| ≤ M ∧
      |spectatorWordDeriv (epsilonNuclearKSPotential i ε Z E) w q| ≤ M := by
    obtain ⟨hbare,hscaled,_⟩ := hbounds ε hε hε1 w.length hw q hq
    exact ⟨(spectatorWordDeriv_abs_le_iteratedFDeriv (nuclearKSCoefficientPatch_isOpen i) hb w (hKpatch hq)).trans hbare,
      (spectatorWordDeriv_abs_le_iteratedFDeriv (nuclearKSCoefficientPatch_isOpen i) hs w (hKpatch hq)).trans hscaled⟩
  refine ⟨hw,?_⟩
  intro a0
  obtain ⟨hlocal,hderiv⟩ := smooth_spectator_source_words (nuclearKSCoefficientPatch_isOpen i) hb (-a0)
  refine ⟨hlocal,hderiv,?_⟩
  intro S hS hSK w hwm
  have hfinite : volume S < ⊤ := (measure_mono hSK).trans_lt hK.measure_lt_top
  simpa only [norm_neg] using
    smooth_spectator_source_region_budget (nuclearKSCoefficientPatch_isOpen i) hb (-a0) w hS
      (hSK.trans hKpatch) hfinite (le_trans (by norm_num) hM)
      (fun q hq => (hw w hwm q (hSK hq)).1)

theorem pairKS_uniform_spectator_word_data (Z E : ℝ)
    {K : Set (PairKSSpace)} (hK : IsCompact K)
    (hKpatch : K ⊆ pairKSCoefficientPatch) (m : ℕ) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
      (∀ w : List (SpectatorCoordinate (0 : Fin 2)), w.length ≤ m → ∀ q ∈ K,
        |spectatorWordDeriv (pairKSPotential Z (ε*E)) w q| ≤ M ∧
        |spectatorWordDeriv (epsilonPairKSPotential ε Z E) w q| ≤ M) ∧
      ∀ a0 : ℂ,
        (∀ w : List (SpectatorCoordinate (0 : Fin 2)), ProductLocallyL2On
          (fun p => spectatorWordDeriv (pairKSPotential Z (ε*E)) w p • (-a0))
          (pairKSCoefficientPatch)) ∧
        (∀ (w : List (SpectatorCoordinate (0 : Fin 2))) (j : SpectatorCoordinate (0 : Fin 2)),
          LocalSpectatorD (pairKSCoefficientPatch)
            (fun p => spectatorWordDeriv (pairKSPotential Z (ε*E)) w p • (-a0))
            (fun p => spectatorWordDeriv (pairKSPotential Z (ε*E)) (j::w) p • (-a0)) j) ∧
        ∀ (S : Set (PairKSSpace)), MeasurableSet S → S ⊆ K →
          ∀ w : List (SpectatorCoordinate (0 : Fin 2)), w.length ≤ m →
            RegionL2Budget
              (fun p => spectatorWordDeriv (pairKSPotential Z (ε*E)) w p • (-a0)) S
              (M^2*‖a0‖^2*(volume S).toReal) := by
  obtain ⟨M,hM,hbounds⟩ := pairKS_uniform_finite_scaled_jets Z E hK hKpatch m
  refine ⟨M,hM,?_⟩
  intro ε hε hε1
  have hb : ContDiffOn ℝ ∞ (pairKSPotential Z (ε*E)) (pairKSCoefficientPatch) := by
    intro q hq
    exact (pairKSPotential_contDiffAt Z (ε*E) hq).contDiffWithinAt
  have hs : ContDiffOn ℝ ∞ (epsilonPairKSPotential ε Z E) (pairKSCoefficientPatch) := by
    intro q hq
    exact (epsilonPairKSPotential_contDiffAt ε Z E hq).contDiffWithinAt
  have hw (w : List (SpectatorCoordinate (0 : Fin 2))) (hw : w.length ≤ m) (q : PairKSSpace)
      (hq : q ∈ K) :
      |spectatorWordDeriv (pairKSPotential Z (ε*E)) w q| ≤ M ∧
      |spectatorWordDeriv (epsilonPairKSPotential ε Z E) w q| ≤ M := by
    obtain ⟨hbare,hscaled,_⟩ := hbounds ε hε hε1 w.length hw q hq
    exact ⟨(spectatorWordDeriv_abs_le_iteratedFDeriv pairKSCoefficientPatch_isOpen hb w (hKpatch hq)).trans hbare,
      (spectatorWordDeriv_abs_le_iteratedFDeriv pairKSCoefficientPatch_isOpen hs w (hKpatch hq)).trans hscaled⟩
  refine ⟨hw,?_⟩
  intro a0
  obtain ⟨hlocal,hderiv⟩ := smooth_spectator_source_words pairKSCoefficientPatch_isOpen hb (-a0)
  refine ⟨hlocal,hderiv,?_⟩
  intro S hS hSK w hwm
  have hfinite : volume S < ⊤ := (measure_mono hSK).trans_lt hK.measure_lt_top
  simpa only [norm_neg] using
    smooth_spectator_source_region_budget pairKSCoefficientPatch_isOpen hb (-a0) w hS
      (hSK.trans hKpatch) hfinite (le_trans (by norm_num) hM)
      (fun q hq => (hw w hwm q (hSK hq)).1)

#print axioms nuclearKS_uniform_spectator_word_data
#print axioms pairKS_uniform_spectator_word_data
end TheoremT.Continuum
