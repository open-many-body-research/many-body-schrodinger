import HardyLimit_v1

/-! Fatou with convergent varying integral bounds. This preserves the limiting
constant during cutoff removal, without assuming integrability of the target. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace TheoremT.HardyLimit

/-- Nonnegative almost-everywhere limits inherit integrability and the limit of
convergent real upper bounds on the approximating integrals. -/
theorem integrable_and_integral_le_of_nonneg_limit_varying_bounds
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ℕ → α → ℝ} {F : α → ℝ} {B : ℕ → ℝ} {b : ℝ}
    (hfi : ∀ n, Integrable (f n) μ)
    (hfn : ∀ n, 0 ≤ᵐ[μ] f n)
    (hF : 0 ≤ᵐ[μ] F)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (F x)))
    (hbound : ∀ n, (∫ x, f n x ∂μ) ≤ B n)
    (hBlim : Tendsto B atTop (𝓝 b)) :
    Integrable F μ ∧ (∫ x, F x ∂μ) ≤ b := by
  have hb : 0 ≤ b := ge_of_tendsto' hBlim
    (fun n => (integral_nonneg_of_ae (hfn n)).trans (hbound n))
  have hmeas : AEStronglyMeasurable F μ :=
    aestronglyMeasurable_of_tendsto_ae _ (fun n => (hfi n).1) hlim
  have hfatou : (∫⁻ x, ENNReal.ofReal (F x) ∂μ) ≤ ENNReal.ofReal b := by
    calc
      (∫⁻ x, ENNReal.ofReal (F x) ∂μ) =
          ∫⁻ x, liminf (fun n => ENNReal.ofReal (f n x)) atTop ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hlim] with x hx
        exact ((ENNReal.continuous_ofReal.tendsto _).comp hx).liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal (f n x) ∂μ) atTop :=
        lintegral_liminf_le' (fun n => (hfi n).aemeasurable.ennreal_ofReal)
      _ ≤ liminf (fun n => ENNReal.ofReal (B n)) atTop := by
        apply liminf_le_liminf
        apply Filter.Eventually.of_forall
        intro n
        rw [← ofReal_integral_eq_lintegral_ofReal (hfi n) (hfn n)]
        exact ENNReal.ofReal_le_ofReal (hbound n)
        all_goals isBoundedDefault
      _ = ENNReal.ofReal b := ((ENNReal.continuous_ofReal.tendsto b).comp hBlim).liminf_eq
  have hint : Integrable F μ :=
    ⟨hmeas, (hasFiniteIntegral_iff_ofReal hF).2
      (lt_of_le_of_lt hfatou ENNReal.ofReal_lt_top)⟩
  refine ⟨hint, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hint hF] at hfatou
  exact (ENNReal.ofReal_le_ofReal_iff hb).1 hfatou

set_option pp.proofs false in
#print integrable_and_integral_le_of_nonneg_limit_varying_bounds
#print axioms integrable_and_integral_le_of_nonneg_limit_varying_bounds
end TheoremT.HardyLimit
