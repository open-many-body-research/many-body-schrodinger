import GenericScaledCutoff_v1
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace TheoremT.Continuum

theorem bounded_real_multiplier_integral_tendsto
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {g : X → ℂ} (hg : Integrable g μ) {a : ℕ → X → ℝ} {c C : ℝ}
    (ha : ∀ n, AEStronglyMeasurable (a n) μ)
    (hb : ∀ n, ∀ᵐ x ∂μ, ‖a n x‖ ≤ C)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun n => a n x) atTop (𝓝 c)) :
    Tendsto (fun n => ∫ x, a n x • g x ∂μ) atTop (𝓝 (∫ x, c • g x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => C*‖g x‖)
  · intro n; exact (ha n).smul hg.aestronglyMeasurable
  · exact hg.norm.const_mul C
  · intro n
    filter_upwards [hb n] with x hx
    simpa only [norm_smul] using mul_le_mul_of_nonneg_right hx (norm_nonneg (g x))
  · filter_upwards [ht] with x hx
    exact hx.smul_const (g x)

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem genericScaledCutoff_sequence_tendsto_one (x : E) :
    Tendsto (fun n : ℕ => genericScaledCutoff E ((n : ℝ)+1) x) atTop (𝓝 1) := by
  have hs : Tendsto (fun n : ℕ => (n : ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  exact (tendsto_const_nhds.congr' (genericScaledCutoff_eventually_one E x).symm).comp hs

theorem genericScaledCutoff_first_sequence (v : E) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ n : ℕ, ∀ x : E, ‖fderiv ℝ (genericScaledCutoff E ((n : ℝ)+1)) x v‖ ≤ C) ∧
      ∀ x : E, Tendsto (fun n : ℕ => fderiv ℝ (genericScaledCutoff E ((n : ℝ)+1)) x v)
        atTop (𝓝 0) := by
  obtain ⟨C,hC,hb⟩ := genericScaledCutoff_partial_bound E v
  have hR (n : ℕ) : (1 : ℝ) ≤ (n : ℝ)+1 := by exact le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ)+1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  refine ⟨C,hC,?_,fun x => ?_⟩
  · intro n x
    exact (hb _ (by positivity) x).trans ((div_le_iff₀ (by positivity)).mpr (by nlinarith [hR n]))
  · apply squeeze_zero_norm (fun n => hb _ (by positivity) x)
    simpa only [div_eq_mul_inv, mul_zero] using hinv.const_mul C

theorem genericScaledCutoff_second_sequence (v w : E) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ n : ℕ, ∀ x : E,
        ‖fderiv ℝ (fun y => fderiv ℝ (genericScaledCutoff E ((n : ℝ)+1)) y v) x w‖ ≤ C) ∧
      ∀ x : E, Tendsto (fun n : ℕ =>
        fderiv ℝ (fun y => fderiv ℝ (genericScaledCutoff E ((n : ℝ)+1)) y v) x w)
        atTop (𝓝 0) := by
  obtain ⟨C,hC,hb⟩ := genericScaledCutoff_second_bound E v w
  have hR (n : ℕ) : (1 : ℝ) ≤ ((n : ℝ)+1)^2 := by nlinarith [sq_nonneg (n : ℝ), Nat.cast_nonneg (α := ℝ) n]
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ)+1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  refine ⟨C,hC,?_,fun x => ?_⟩
  · intro n x
    exact (hb _ (by positivity) x).trans ((div_le_iff₀ (by positivity)).mpr (by nlinarith [hR n]))
  · apply squeeze_zero_norm (fun n => hb _ (by positivity) x)
    simpa only [div_eq_mul_inv, inv_pow, zero_pow (by decide : 2 ≠ 0), mul_zero] using (hinv.pow 2).const_mul C

#print axioms bounded_real_multiplier_integral_tendsto
#print axioms genericScaledCutoff_second_sequence
end TheoremT.Continuum
