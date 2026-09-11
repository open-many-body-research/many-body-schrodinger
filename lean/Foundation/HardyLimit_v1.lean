import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-! Fatou bridge for the regularized Hardy weight. This file proves the limit step,
not the regularized Hardy estimate supplied as a hypothesis. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace TheoremT.HardyLimit

/-- Uniform bounds for nonnegative integrable approximants pass to an a.e. limit,
and prove integrability of the limit. No domination assumption is required. -/
theorem integrable_and_integral_le_of_nonneg_limit
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ℕ → α → ℝ} {F : α → ℝ} {B : ℝ}
    (hfi : ∀ n, Integrable (f n) μ)
    (hfn : ∀ n, 0 ≤ᵐ[μ] f n)
    (hF : 0 ≤ᵐ[μ] F)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (F x)))
    (hbound : ∀ n, (∫ x, f n x ∂μ) ≤ B) (hB : 0 ≤ B) :
    Integrable F μ ∧ (∫ x, F x ∂μ) ≤ B := by
  have hmeas : AEStronglyMeasurable F μ :=
    aestronglyMeasurable_of_tendsto_ae _ (fun n => (hfi n).1) hlim
  have hfatou : (∫⁻ x, ENNReal.ofReal (F x) ∂μ) ≤ ENNReal.ofReal B := by
    calc
      (∫⁻ x, ENNReal.ofReal (F x) ∂μ) =
          ∫⁻ x, liminf (fun n => ENNReal.ofReal (f n x)) atTop ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hlim] with x hx
        exact ((ENNReal.continuous_ofReal.tendsto _).comp hx).liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal (f n x) ∂μ) atTop :=
        lintegral_liminf_le' (fun n => (hfi n).aemeasurable.ennreal_ofReal)
      _ ≤ ENNReal.ofReal B := by
        apply liminf_le_of_frequently_le'
        apply Filter.Frequently.of_forall
        intro n
        rw [← ofReal_integral_eq_lintegral_ofReal (hfi n) (hfn n)]
        exact ENNReal.ofReal_le_ofReal (hbound n)
  have hint : Integrable F μ :=
    ⟨hmeas, (hasFiniteIntegral_iff_ofReal hF).2
      (lt_of_le_of_lt hfatou ENNReal.ofReal_lt_top)⟩
  refine ⟨hint, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hint hF] at hfatou
  exact (ENNReal.ofReal_le_ofReal_iff hB).1 hfatou

#print axioms integrable_and_integral_le_of_nonneg_limit
end TheoremT.HardyLimit
