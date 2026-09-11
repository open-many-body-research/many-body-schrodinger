import HardyLimit_v1
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.L2Space

/-! The regularization-to-singular-weight step for real compactly supported continuous
functions on genuine Euclidean R³. The regularized inequality is an explicit
hypothesis; this is not by itself a proof of Hardy's inequality. -/
noncomputable section
set_option maxHeartbeats 400000
open MeasureTheory Filter
open scoped Topology
namespace TheoremT.HardyLimit

abbrev R3 := EuclideanSpace ℝ (Fin 3)

/-- Compact continuity proves every positive regularization is integrable. -/
theorem regularizedWeight_integrable {u : R3 → ℝ}
    (hu : Continuous u) (huc : HasCompactSupport u)
    {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun x => (u x)^2 / (‖x‖^2 + δ)) := by
  have hpos : ∀ x : R3, 0 < ‖x‖^2 + δ :=
    fun x => add_pos_of_nonneg_of_pos (sq_nonneg _) hδ
  have hc : Continuous (fun x : R3 => (u x)^2 / (‖x‖^2 + δ)) :=
    (hu.pow 2).div ((continuous_norm.pow 2).add continuous_const) (fun x => (hpos x).ne')
  apply hc.integrable_of_hasCompactSupport
  apply huc.mono
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  intro hz
  apply hx
  rw [hz]
  simp only [zero_pow (by norm_num : 2 ≠ 0), zero_div]

/-- Removing the regularization concludes actual integrability of the singular
weighted square and the same real bound. The value at the origin is irrelevant
because its Lebesgue measure is zero. -/
theorem singularWeight_of_regularized_bounds {u : R3 → ℝ} {B : ℝ}
    (hu : Continuous u) (huc : HasCompactSupport u)
    (hbound : ∀ δ : ℝ, 0 < δ → (∫ x, (u x)^2 / (‖x‖^2 + δ)) ≤ B) :
    Integrable (fun x => (u x)^2 / ‖x‖^2) ∧
      (∫ x, (u x)^2 / ‖x‖^2) ≤ B := by
  let δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hδ : ∀ n, 0 < δ n := by intro n; dsimp [δ]; positivity
  have hint : ∀ n, Integrable (fun x : R3 => (u x)^2 / (‖x‖^2 + δ n)) :=
    fun n => regularizedWeight_integrable hu huc (hδ n)
  have hnonneg : ∀ n, 0 ≤ᵐ[volume] (fun x : R3 => (u x)^2 / (‖x‖^2 + δ n)) := by
    intro n
    exact Filter.Eventually.of_forall (fun x => div_nonneg (sq_nonneg _) (by positivity))
  have hB : 0 ≤ B := le_trans (integral_nonneg_of_ae (hnonneg 0)) (hbound (δ 0) (hδ 0))
  apply integrable_and_integral_le_of_nonneg_limit hint hnonneg
  · exact Filter.Eventually.of_forall (fun x => div_nonneg (sq_nonneg _) (sq_nonneg _))
  · filter_upwards [volume.ae_ne (0 : R3)] with x hx
    have hdlim : Tendsto δ atTop (𝓝 (0 : ℝ)) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hden : Tendsto (fun n => ‖x‖^2 + δ n) atTop (𝓝 (‖x‖^2)) := by
      simpa using tendsto_const_nhds.add hdlim
    exact tendsto_const_nhds.div hden (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))
  · exact fun n => hbound (δ n) (hδ n)
  · exact hB

#print singularWeight_of_regularized_bounds
#print axioms singularWeight_of_regularized_bounds
end TheoremT.HardyLimit
