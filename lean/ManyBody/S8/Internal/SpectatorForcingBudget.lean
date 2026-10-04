import ManyBody.S8.Internal.SpectatorBootstrap
import ManyBody.S8.Internal.NuclearChartDerivativeBounds
import ManyBody.S8.Internal.NuclearChartBounds

/-! An actual local integral bound on the principal forcing in the first
spectator bootstrap. Both coefficient bounds can be discharged on the physical
chart; the energy contributes to the coefficient but not its spectator derivative.
-/
noncomputable section
open MeasureTheory
open scoped ContDiff
open TheoremT.Continuum TheoremT.Continuum.WeakGrushin

namespace ManyBody.S8
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem bounded_spectator_forcing_integral_le
    {Ω K : Set (Space κ)} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {B : Space κ → ℝ} (hB : ContDiffOn ℝ ∞ B Ω)
    (U d : Lp ℂ 2 (volume : Measure (Space κ))) (j : κ)
    {b b1 : ℝ} (_hb : 0 ≤ b) (_hb1 : 0 ≤ b1)
    (hBb : ∀ p ∈ K, ‖B p‖ ≤ b)
    (hDb : ∀ p ∈ K, ‖fderiv ℝ B p (tDir j)‖ ≤ b1) :
    (∫ p in K, ‖-(fderiv ℝ B p (tDir j) • U p) - B p • d p‖ ^ 2) ≤
      2 * b1 ^ 2 * (∫ p in K, ‖U p‖ ^ 2) +
      2 * b ^ 2 * (∫ p in K, ‖d p‖ ^ 2) := by
  have hcoeff := smooth_coefficient_and_directional_memLp_top_restrict_compact
    (μ := volume) hΩ hK hKΩ hB (tDir j)
  have hUl : MemLp (U : Space κ → ℂ) 2 (volume.restrict K) := (Lp.memLp U).mono_measure Measure.restrict_le_self
  have hdl : MemLp (d : Space κ → ℂ) 2 (volume.restrict K) := (Lp.memLp d).mono_measure Measure.restrict_le_self
  have hsource : MemLp (fun p => -(fderiv ℝ B p (tDir j) • U p) - B p • d p) 2 (volume.restrict K) := (hUl.smul hcoeff.2).neg.sub (hdl.smul hcoeff.1)
  have hi := hsource.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hiU := hUl.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hid := hdl.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  calc
    _ ≤ ∫ p in K, 2 * b1 ^ 2 * ‖U p‖ ^ 2 + 2 * b ^ 2 * ‖d p‖ ^ 2 := by
      apply integral_mono_ae hi ((hiU.const_mul _).add (hid.const_mul _))
      filter_upwards [ae_restrict_mem hK.measurableSet] with p hp
      have hn : ‖-(fderiv ℝ B p (tDir j) • U p) - B p • d p‖ ≤
          b1 * ‖U p‖ + b * ‖d p‖ := by
        calc
          _ ≤ ‖-(fderiv ℝ B p (tDir j) • U p)‖ + ‖B p • d p‖ := norm_sub_le _ _
          _ = ‖fderiv ℝ B p (tDir j)‖ * ‖U p‖ + ‖B p‖ * ‖d p‖ := by
            rw [norm_neg, norm_smul, norm_smul]
          _ ≤ _ := add_le_add
            (mul_le_mul_of_nonneg_right (hDb p hp) (norm_nonneg _))
            (mul_le_mul_of_nonneg_right (hBb p hp) (norm_nonneg _))
      have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
      change ‖-(fderiv ℝ B p (tDir j) • U p) - B p • d p‖ ^ 2 ≤
        2 * b1 ^ 2 * ‖U p‖ ^ 2 + 2 * b ^ 2 * ‖d p‖ ^ 2
      nlinarith [sq_nonneg (b1 * ‖U p‖ - b * ‖d p‖)]
    _ = _ := by
      rw [integral_add (hiU.const_mul _) (hid.const_mul _), integral_const_mul, integral_const_mul]

theorem nuclear_chart_spectator_forcing_integral_le
    (Z E : ℝ) (t0 : Position) (ht0 : ‖t0‖ = 1)
    {K : Set (NuclearKSSpace (0 : Fin 2))} (hK : IsCompact K)
    (hKΩ : K ⊆ nuclearChartOpen t0)
    (U d : Lp ℂ 2 (volume : Measure (NuclearKSSpace (0 : Fin 2))))
    (j : SpectatorCoordinate (0 : Fin 2)) :
    (∫ p in K, ‖-(fderiv ℝ (nuclearKSPotential (0 : Fin 2) Z E) p (tDir j) • U p) -
        nuclearKSPotential (0 : Fin 2) Z E p • d p‖ ^ 2) ≤
      2 * ((8 / 9 : ℝ) * |Z| + 128 / 121) ^ 2 * (∫ p in K, ‖U p‖ ^ 2) +
      2 * ((26 / 3 : ℝ) * |Z| + 8 / 11 + |E| / 2) ^ 2 * (∫ p in K, ‖d p‖ ^ 2) := by
  have hB : ContDiffOn ℝ ∞ (nuclearKSPotential (0 : Fin 2) Z E) (nuclearChartOpen t0) := by
    intro p hp
    exact (nuclearKSPotential_contDiffAt (0 : Fin 2) Z E
      (nuclearChartOpen_subset_coefficientPatch t0 ht0 hp)).contDiffWithinAt
  apply bounded_spectator_forcing_integral_le (nuclearChartOpen_isOpen t0) hK hKΩ hB U d j
    (by positivity) (by positivity)
  · intro p hp
    exact nuclearKSPotential_norm_le_of_mem_nuclearChartOpen Z E t0 ht0 (hKΩ hp)
  · intro p hp
    simpa only [Real.norm_eq_abs] using
      nuclearKSPotential_spectator_abs_le_of_mem_nuclearChartOpen Z E t0 ht0 (hKΩ hp) j

#print axioms bounded_spectator_forcing_integral_le
#print axioms nuclear_chart_spectator_forcing_integral_le
end ManyBody.S8