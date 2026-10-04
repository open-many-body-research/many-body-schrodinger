import WeakGrushinMixedMultiIndexEquation_v1
import GrushinFactorialPotentialWordBound_v1

/-! The sealed ordered R16 norm estimate for the actual potential
commutator appearing in the differentiated weak equation. Coefficient
measurability and factorial bounds refer to its ordinary directional
word derivatives. Shifted outer representatives and their lower-order
norm bounds remain explicit premises of this finite estimate.
-/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin

theorem factorial_actual_potential_commutator_L2
    {μ : Measure (Space (Fin 3))} (F : FactorialRawJetFamily)
    (W : (Fin 4 → ℕ) → (Fin 3 → ℕ) → FactorialOuterIndex → Lp ℂ 2 μ)
    (r : ℕ) (N : ℕ → ℝ) (hN0 : ∀ k, 0 ≤ N k)
    (hW : ∀ a b, factorialMultiDerivativeCost a b ≤ r-1 → FactorialShiftedOuterL2Rep F W a b)
    (hN : ∀ k, k ≤ r-1 → ∀ a b, factorialMultiDerivativeCost a b ≤ k → factorialOuterNorm (W a b) ≤ N k)
    (B : Space (Fin 3) → ℝ) (M A : ℝ) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hBmeas : ∀ v, v.length ≤ r →
      AEStronglyMeasurable (directionalWordDeriv productCoordinateDirection B v) μ)
    (hBbound : ∀ v, v.length ≤ r → ∀ᵐ p ∂μ,
      |directionalWordDeriv productCoordinateDirection B v p| ≤
        M*A^v.length*(v.length.factorial : ℝ))
    (w : List (Fin 4 ⊕ Fin 3))
    (hc : factorialMultiDerivativeCost (factorialWordYCount w) (factorialWordTCount w) ≤ r) :
    ∃ H : Lp ℂ 2 μ,
      H =ᵐ[μ] directionalWordCommutator productCoordinateDirection B (mixedMultiIndexWordFamily F) w ∧
      ‖H‖ ≤ M*(∑ j ∈ Finset.range r, (r.choose (j+1) : ℝ)*A^(j+1)*
        ((j+1).factorial : ℝ)*N (r-(j+1))) := by
  unfold directionalWordCommutator mixedMultiIndexWordFamily
  exact factorial_potential_word_error_L2 F W r N hN0 hW hN
      (directionalWordDeriv productCoordinateDirection B) M A hM hA hBmeas hBbound w hc


theorem factorial_actual_potential_commutator_on_compact_L2
    {Ω K : Set (Space (Fin 3))} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (F : FactorialRawJetFamily)
    (W : (Fin 4 → ℕ) → (Fin 3 → ℕ) → FactorialOuterIndex → Lp ℂ 2 (volume.restrict K))
    (r : ℕ) (N : ℕ → ℝ) (hN0 : ∀ k, 0 ≤ N k)
    (hW : ∀ a b, factorialMultiDerivativeCost a b ≤ r-1 → FactorialShiftedOuterL2Rep F W a b)
    (hN : ∀ k, k ≤ r-1 → ∀ a b, factorialMultiDerivativeCost a b ≤ k → factorialOuterNorm (W a b) ≤ N k)
    {B : Space (Fin 3) → ℝ} (hB : ContDiffOn ℝ ∞ B Ω)
    (M A : ℝ) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hBbound : ∀ v, v.length ≤ r → ∀ p ∈ K,
      |directionalWordDeriv productCoordinateDirection B v p| ≤
        M*A^v.length*(v.length.factorial : ℝ))
    (w : List (Fin 4 ⊕ Fin 3))
    (hc : factorialMultiDerivativeCost (factorialWordYCount w) (factorialWordTCount w) ≤ r) :
    ∃ H : Lp ℂ 2 (volume.restrict K),
      H =ᵐ[volume.restrict K]
        directionalWordCommutator productCoordinateDirection B (mixedMultiIndexWordFamily F) w ∧
      ‖H‖ ≤ M*(∑ j ∈ Finset.range r, (r.choose (j+1) : ℝ)*A^(j+1)*
        ((j+1).factorial : ℝ)*N (r-(j+1))) := by
  apply factorial_actual_potential_commutator_L2 F W r N hN0 hW hN B M A hM hA
  · intro v hv
    exact ((directionalWordDeriv_contDiffOn productCoordinateDirection hΩ hB v).continuousOn.mono
      hKΩ).aestronglyMeasurable hK.measurableSet
  · intro v hv
    filter_upwards [ae_restrict_mem hK.measurableSet] with p hp
    exact hBbound v hv p hp
  · exact hc

#print axioms factorial_actual_potential_commutator_L2
#print axioms factorial_actual_potential_commutator_on_compact_L2
end TheoremT.Continuum.WeakGrushin
