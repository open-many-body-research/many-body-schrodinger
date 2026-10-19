import CompactSupportWeightedL2_v1
import GrushinFactorialMonomialBound_v1
import GrushinRectangularBoxGeometry_v1
import SpectatorIterationState_v1

/-! Continuous real weights preserve actual local L2 membership on a region
contained in a compact set. The bounded compact indicator agrees with the
weight almost everywhere for the restricted measure. The region itself need
not be measurable for this argument. No weighted norm is an input. -/
noncomputable section
open MeasureTheory Filter
namespace TheoremT.Continuum.WeakGrushin

theorem restricted_compact_weight_memLp
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} {Ω K : Set E} (hK : IsCompact K) (hΩK : Ω ⊆ K)
    (χ : E → ℝ) (hχ : Continuous χ) {F : E → ℂ}
    (hF : MemLp F 2 (μ.restrict Ω)) :
    MemLp (fun p => χ p • F p) 2 (μ.restrict Ω) := by
  classical
  have htop : MemLp (K.indicator χ) ⊤ (μ.restrict Ω) :=
    compact_indicator_continuous_memLp_top hK hχ
  have hmem : ∀ᵐ p ∂μ.restrict Ω, p ∈ K :=
    ae_restrict_of_ae_restrict_of_subset hΩK (ae_restrict_mem hK.measurableSet)
  apply (hF.smul htop).ae_eq
  filter_upwards [hmem] with p hp
  change K.indicator χ p • F p = χ p • F p
  rw [Set.indicator_of_mem hp]

theorem rectangular_continuous_weight_memLp
    (a : Space (Fin 3)) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (χ : Space (Fin 3) → ℝ) (hχ : Continuous χ) {F : Space (Fin 3) → ℂ}
    (hF : MemLp F 2 (volume.restrict (rectangularOpenBox a A B))) :
    MemLp (fun p => χ p • F p) 2 (volume.restrict (rectangularOpenBox a A B)) :=
  restricted_compact_weight_memLp (rectangularClosedBox_isCompact a hA hB)
    (rectangularOpenBox_subset_closedBox a A B) χ hχ hF

theorem rectangular_factorial_monomial_memLp
    (a : Space (Fin 3)) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (γ : Fin 4 → ℕ) {F : Space (Fin 3) → ℂ}
    (hF : MemLp F 2 (volume.restrict (rectangularOpenBox a A B))) :
    MemLp (fun p => factorialYMonomial γ p.1 • F p) 2
      (volume.restrict (rectangularOpenBox a A B)) :=
  rectangular_continuous_weight_memLp a hA hB _
    ((factorialYMonomial_continuous γ).comp continuous_fst) hF

theorem regionL2Budget_rectangular_factorial_monomial_memLp
    (a : Space (Fin 3)) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (γ : Fin 4 → ℕ) {F : Space (Fin 3) → ℂ} {W : ℝ}
    (hF : RegionL2Budget F (rectangularOpenBox a A B) W) :
    MemLp (fun p => factorialYMonomial γ p.1 • F p) 2
      (volume.restrict (rectangularOpenBox a A B)) :=
  rectangular_factorial_monomial_memLp a hA hB γ hF.1

end TheoremT.Continuum.WeakGrushin
