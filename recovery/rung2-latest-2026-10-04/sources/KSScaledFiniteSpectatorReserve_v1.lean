import KSScaledSpectatorWordBudgets_v1
import SpectatorFiniteIteration_v1

/-! Actual physical scaled-coefficient finite spectator reserve. Only the raw
solution region L2 budget and the undifferentiated weak equation are inputs.
Coefficient and forcing words, their weak links, and every solution derivative
used by the n-stage iteration are derived. The cutoff geometry is explicit
input data; no terminal region beyond its actual n stages is silently used. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum
open WeakGrushin

theorem nuclearKS_scaled_finite_spectator_reserve {N : ℕ} (i : Fin N)
    (Z E : ℝ)
    {K : Set (NuclearKSSpace i)} (hK : IsCompact K)
    (hKpatch : K ⊆ nuclearKSCoefficientPatch i) (n : ℕ) :
    ∃ K0 : ℝ, 1 ≤ K0 ∧
      ∀ (Ω W : ℕ → Set (NuclearKSSpace i)) (χ η : ℕ → NuclearKSSpace i → ℝ)
        (M A B D Q : ℕ → ℝ),
        (∀ k, k < n → SpectatorStepGeometry 4 (Ω k) (Ω (k+1)) (W k)
          (χ k) (η k) (M k) (A k) (B k) (D k) (Q k)) →
        MeasurableSet (Ω 0) → Ω 0 ⊆ K →
        ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ (a0 : ℂ) (f : NuclearKSSpace i → ℂ) (Winit : ℝ),
          0 ≤ Winit → RegionL2Budget f (Ω 0) Winit →
          (∀ φ : NuclearKSSpace i → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω 0 →
            (∫ p, splitGrushin 4 oscillatorBasis (epsilonNuclearKSPotential i ε Z E) φ p • f p) =
              ∫ p, φ p • ((nuclearKSPotential i Z (ε*E)) p • (-a0))) →
          0 ≤ spectatorIterationBudgetSeq 4 M A B D Q K0
            (K0^2*‖a0‖^2*(volume (Ω 0)).toReal) Winit n ∧
          SpectatorFiniteState (Ω n) f n
            (spectatorIterationBudgetSeq 4 M A B D Q K0
              (K0^2*‖a0‖^2*(volume (Ω 0)).toReal) Winit n) := by
  obtain ⟨K0,hK0,hdata⟩ := nuclearKS_uniform_spectator_word_data i Z E hK hKpatch (n-1)
  refine ⟨K0,hK0,?_⟩
  intro Ω W χ η M A B D Q hGeom hΩmeas hΩK ε hε hε1 a0 f Winit hWinit hf hEq
  obtain ⟨hcoeff,hsource⟩ := hdata ε hε hε1
  obtain ⟨_hlocal,hderiv,hbudget⟩ := hsource a0
  have hΩpatch : Ω 0 ⊆ nuclearKSCoefficientPatch i := hΩK.trans hKpatch
  have hP : ContDiffOn ℝ ∞ (epsilonNuclearKSPotential i ε Z E) (Ω 0) := by
    intro p hp
    exact (epsilonNuclearKSPotential_contDiffAt i ε Z E (hΩpatch hp)).contDiffWithinAt
  exact spectatorFiniteState_iterate (by norm_num : (0 : ℝ) < 4) n Ω W χ η M A B D Q
    hGeom hP f
    (fun w p => spectatorWordDeriv (nuclearKSPotential i Z (ε*E)) w p • (-a0))
    K0 Winit (K0^2*‖a0‖^2*(volume (Ω 0)).toReal)
    (le_trans (by norm_num) hK0) hWinit (by positivity) hf
    (fun w hw => hbudget (Ω 0) hΩmeas hΩK w (by omega))
    (fun w j _hw => (hderiv w j).mono hΩpatch)
    (fun w hw p hp => (hcoeff w (by omega) p (hΩK hp)).2)
    hEq

theorem pairKS_scaled_finite_spectator_reserve (Z E : ℝ)
    {K : Set (PairKSSpace)} (hK : IsCompact K)
    (hKpatch : K ⊆ pairKSCoefficientPatch) (n : ℕ) :
    ∃ K0 : ℝ, 1 ≤ K0 ∧
      ∀ (Ω W : ℕ → Set (PairKSSpace)) (χ η : ℕ → PairKSSpace → ℝ)
        (M A B D Q : ℕ → ℝ),
        (∀ k, k < n → SpectatorStepGeometry 1 (Ω k) (Ω (k+1)) (W k)
          (χ k) (η k) (M k) (A k) (B k) (D k) (Q k)) →
        MeasurableSet (Ω 0) → Ω 0 ⊆ K →
        ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ (a0 : ℂ) (f : PairKSSpace → ℂ) (Winit : ℝ),
          0 ≤ Winit → RegionL2Budget f (Ω 0) Winit →
          (∀ φ : PairKSSpace → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω 0 →
            (∫ p, splitGrushin 1 oscillatorBasis (epsilonPairKSPotential ε Z E) φ p • f p) =
              ∫ p, φ p • ((pairKSPotential Z (ε*E)) p • (-a0))) →
          0 ≤ spectatorIterationBudgetSeq 1 M A B D Q K0
            (K0^2*‖a0‖^2*(volume (Ω 0)).toReal) Winit n ∧
          SpectatorFiniteState (Ω n) f n
            (spectatorIterationBudgetSeq 1 M A B D Q K0
              (K0^2*‖a0‖^2*(volume (Ω 0)).toReal) Winit n) := by
  obtain ⟨K0,hK0,hdata⟩ := pairKS_uniform_spectator_word_data Z E hK hKpatch (n-1)
  refine ⟨K0,hK0,?_⟩
  intro Ω W χ η M A B D Q hGeom hΩmeas hΩK ε hε hε1 a0 f Winit hWinit hf hEq
  obtain ⟨hcoeff,hsource⟩ := hdata ε hε hε1
  obtain ⟨_hlocal,hderiv,hbudget⟩ := hsource a0
  have hΩpatch : Ω 0 ⊆ pairKSCoefficientPatch := hΩK.trans hKpatch
  have hP : ContDiffOn ℝ ∞ (epsilonPairKSPotential ε Z E) (Ω 0) := by
    intro p hp
    exact (epsilonPairKSPotential_contDiffAt ε Z E (hΩpatch hp)).contDiffWithinAt
  exact spectatorFiniteState_iterate (by norm_num : (0 : ℝ) < 1) n Ω W χ η M A B D Q
    hGeom hP f
    (fun w p => spectatorWordDeriv (pairKSPotential Z (ε*E)) w p • (-a0))
    K0 Winit (K0^2*‖a0‖^2*(volume (Ω 0)).toReal)
    (le_trans (by norm_num) hK0) hWinit (by positivity) hf
    (fun w hw => hbudget (Ω 0) hΩmeas hΩK w (by omega))
    (fun w j _hw => (hderiv w j).mono hΩpatch)
    (fun w hw p hp => (hcoeff w (by omega) p (hΩK hp)).2)
    hEq

#print axioms nuclearKS_scaled_finite_spectator_reserve
#print axioms pairKS_scaled_finite_spectator_reserve
end TheoremT.Continuum
