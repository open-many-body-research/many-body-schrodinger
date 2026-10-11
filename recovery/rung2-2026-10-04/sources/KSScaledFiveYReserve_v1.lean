import KSScaledMixedWordBudgets_v1
import MixedYFiveStepReserve_v1
import GrushinQuadraticYWordBound_v1

/-! Five actual Y stages for the physical scaled nuclear and pair KS
coefficients. All order-ten mixed source/coefficient inputs are discharged.
The remaining inputs are actual cutoff geometry, the original normalized
forcing equation, and a genuine initial spectator reserve. Constants are
chosen before epsilon, source amplitude, geometry and the raw solution. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum
open WeakGrushin

theorem nuclearKS_scaled_five_y_reserve {N : ℕ} (i : Fin N)
    (Z E : ℝ)
    {K : Set (NuclearKSSpace i)} (hK : IsCompact K) (hKpatch : K ⊆ nuclearKSCoefficientPatch i) :
    ∃ K0 Q0 : ℝ, 1 ≤ K0 ∧ 0 ≤ Q0 ∧
      ∀ (Ω V : ℕ → Set (NuclearKSSpace i)) (χ η : ℕ → NuclearKSSpace i → ℝ) (M A L D Q : ℕ → ℝ),
        (∀ k, k < 5 → SpectatorStepGeometry 0 (Ω k) (Ω (k+1)) (V k)
          (χ k) (η k) (M k) (A k) (L k) (D k) (Q k)) →
        (∀ k, k < 5 → IsOpen (Ω (k+1))) → Ω 0 ⊆ K →
        ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ (a0 : ℂ) (f : NuclearKSSpace i → ℂ) (Winit : ℝ),
          0 ≤ Winit → SpectatorFiniteState (Ω 0) f 12 Winit →
          (∀ φ : NuclearKSSpace i → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω 0 →
            (∫ p, splitGrushin 4 oscillatorBasis (epsilonNuclearKSPotential i ε Z E) φ p • f p) =
              ∫ p, φ p • ((nuclearKSPotential i Z (ε*E)) p • (-a0))) →
          0 ≤ mixedYIterationBudgetSeq 4 M A L D Q K0 Q0
            (K0^2*‖a0‖^2*(volume (Ω 0)).toReal) 12 (Fintype.card (SpectatorCoordinate i)) Winit 5 ∧
          MixedTriangularState (Ω 5) f 12 12
            (mixedYIterationBudgetSeq 4 M A L D Q K0 Q0
              (K0^2*‖a0‖^2*(volume (Ω 0)).toReal) 12 (Fintype.card (SpectatorCoordinate i)) Winit 5) := by
  obtain ⟨K0,hK0,hdata⟩ := nuclearKS_uniform_mixed_word_data i Z E hK hKpatch 10
  obtain ⟨R,hR⟩ := hK.exists_bound_of_continuousOn
    (show ContinuousOn (fun p : NuclearKSSpace i => p.1) K from continuous_fst.continuousOn)
  let Q0 := grushinQuadraticYWordBound (max 0 R)
  have hQ0 : 0 ≤ Q0 := grushinQuadraticYWordBound_nonneg (le_max_left _ _)
  have hQuadK (a : List (Fin 4)) (p : NuclearKSSpace i) (hp : p ∈ K) :
      |directionalWordDeriv yDir (fun q : NuclearKSSpace i => ‖q.1‖^2) a p| ≤ Q0 := by
    simpa only [Real.norm_eq_abs] using
      grushin_quadratic_y_word_bound_on (le_max_left 0 R)
        (fun q hq => (hR q hq).trans (le_max_right 0 R)) a p hp
  refine ⟨K0,Q0,hK0,hQ0,?_⟩
  intro Ω V χ η M A L D Q hGeom hO hΩK ε hε hε1 a0 f Winit hWinit hf hEq
  obtain ⟨hcoeff,hsource⟩ := hdata ε hε hε1
  obtain ⟨_hlocal,hSY,hST,hbudget⟩ := hsource a0
  have hΩpatch : Ω 0 ⊆ nuclearKSCoefficientPatch i := hΩK.trans hKpatch
  have hΩ : IsOpen (Ω 0) := (hGeom 0 (by norm_num)).1
  have hB : ContDiffOn ℝ ∞ (epsilonNuclearKSPotential i ε Z E) (Ω 0) := by
    intro p hp
    exact (epsilonNuclearKSPotential_contDiffAt i ε Z E (hΩpatch hp)).contDiffWithinAt
  exact spectatorFiniteState_five_y_steps 4 Ω V χ η M A L D Q hGeom hO hB
    K0 Q0 (K0^2*‖a0‖^2*(volume (Ω 0)).toReal) Winit hWinit f
    (fun a t p => directionalWordDeriv yDir (spectatorWordDeriv (nuclearKSPotential i Z (ε*E)) t) a p • (-a0)) hf
    (fun a t hat => hbudget (Ω 0) hΩ.measurableSet hΩK a t hat)
    (fun a t j _hat => (hSY a t j).mono hΩpatch)
    (fun t j _ht => (hST t j).mono hΩpatch)
    (fun a t hat p hp => (hcoeff a t hat p (hΩK hp)).2)
    (fun a _ha p hp => hQuadK a p (hΩK hp)) hEq

theorem pairKS_scaled_five_y_reserve (Z E : ℝ)
    {K : Set (PairKSSpace)} (hK : IsCompact K) (hKpatch : K ⊆ pairKSCoefficientPatch) :
    ∃ K0 Q0 : ℝ, 1 ≤ K0 ∧ 0 ≤ Q0 ∧
      ∀ (Ω V : ℕ → Set (PairKSSpace)) (χ η : ℕ → PairKSSpace → ℝ) (M A L D Q : ℕ → ℝ),
        (∀ k, k < 5 → SpectatorStepGeometry 0 (Ω k) (Ω (k+1)) (V k)
          (χ k) (η k) (M k) (A k) (L k) (D k) (Q k)) →
        (∀ k, k < 5 → IsOpen (Ω (k+1))) → Ω 0 ⊆ K →
        ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ (a0 : ℂ) (f : PairKSSpace → ℂ) (Winit : ℝ),
          0 ≤ Winit → SpectatorFiniteState (Ω 0) f 12 Winit →
          (∀ φ : PairKSSpace → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω 0 →
            (∫ p, splitGrushin 1 oscillatorBasis (epsilonPairKSPotential ε Z E) φ p • f p) =
              ∫ p, φ p • ((pairKSPotential Z (ε*E)) p • (-a0))) →
          0 ≤ mixedYIterationBudgetSeq 1 M A L D Q K0 Q0
            (K0^2*‖a0‖^2*(volume (Ω 0)).toReal) 12 (Fintype.card (SpectatorCoordinate (0 : Fin 2))) Winit 5 ∧
          MixedTriangularState (Ω 5) f 12 12
            (mixedYIterationBudgetSeq 1 M A L D Q K0 Q0
              (K0^2*‖a0‖^2*(volume (Ω 0)).toReal) 12 (Fintype.card (SpectatorCoordinate (0 : Fin 2))) Winit 5) := by
  obtain ⟨K0,hK0,hdata⟩ := pairKS_uniform_mixed_word_data Z E hK hKpatch 10
  obtain ⟨R,hR⟩ := hK.exists_bound_of_continuousOn
    (show ContinuousOn (fun p : PairKSSpace => p.1) K from continuous_fst.continuousOn)
  let Q0 := grushinQuadraticYWordBound (max 0 R)
  have hQ0 : 0 ≤ Q0 := grushinQuadraticYWordBound_nonneg (le_max_left _ _)
  have hQuadK (a : List (Fin 4)) (p : PairKSSpace) (hp : p ∈ K) :
      |directionalWordDeriv yDir (fun q : PairKSSpace => ‖q.1‖^2) a p| ≤ Q0 := by
    simpa only [Real.norm_eq_abs] using
      grushin_quadratic_y_word_bound_on (le_max_left 0 R)
        (fun q hq => (hR q hq).trans (le_max_right 0 R)) a p hp
  refine ⟨K0,Q0,hK0,hQ0,?_⟩
  intro Ω V χ η M A L D Q hGeom hO hΩK ε hε hε1 a0 f Winit hWinit hf hEq
  obtain ⟨hcoeff,hsource⟩ := hdata ε hε hε1
  obtain ⟨_hlocal,hSY,hST,hbudget⟩ := hsource a0
  have hΩpatch : Ω 0 ⊆ pairKSCoefficientPatch := hΩK.trans hKpatch
  have hΩ : IsOpen (Ω 0) := (hGeom 0 (by norm_num)).1
  have hB : ContDiffOn ℝ ∞ (epsilonPairKSPotential ε Z E) (Ω 0) := by
    intro p hp
    exact (epsilonPairKSPotential_contDiffAt ε Z E (hΩpatch hp)).contDiffWithinAt
  exact spectatorFiniteState_five_y_steps 1 Ω V χ η M A L D Q hGeom hO hB
    K0 Q0 (K0^2*‖a0‖^2*(volume (Ω 0)).toReal) Winit hWinit f
    (fun a t p => directionalWordDeriv yDir (spectatorWordDeriv (pairKSPotential Z (ε*E)) t) a p • (-a0)) hf
    (fun a t hat => hbudget (Ω 0) hΩ.measurableSet hΩK a t hat)
    (fun a t j _hat => (hSY a t j).mono hΩpatch)
    (fun t j _ht => (hST t j).mono hΩpatch)
    (fun a t hat p hp => (hcoeff a t hat p (hΩK hp)).2)
    (fun a _ha p hp => hQuadK a p (hΩK hp)) hEq

#print axioms nuclearKS_scaled_five_y_reserve
#print axioms pairKS_scaled_five_y_reserve
end TheoremT.Continuum
