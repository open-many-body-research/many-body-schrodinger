import CutoffConvergence_v2

/-! Dominated convergence in the actual configuration-space L2 classes.
No finite measure of the entire configuration space is assumed. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace TheoremT.Continuum

theorem configuration_toLp_tendsto_dominated {N : ℕ}
    {F : ℕ → Configuration N → ℂ} {f : Configuration N → ℂ}
    {bound : Configuration N → ℝ}
    (hF : ∀ n, MemLp (F n) 2 volume) (hf : MemLp f 2 volume) (hb : MemLp bound 2 volume)
    (hFn : ∀ n, ∀ᵐ x, ‖F n x‖ ≤ ‖bound x‖)
    (hfn : ∀ᵐ x, ‖f x‖ ≤ ‖bound x‖)
    (hlim : ∀ᵐ x, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    Tendsto (fun n => (hF n).toLp (F n)) atTop (𝓝 (hf.toLp f)) := by
  let H : Configuration N → ℝ := fun x => (2*‖bound x‖)^2
  have hHi : Integrable H volume := by
    have hi := (hb.const_smul (2:ℝ)).integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)
    simpa [H,norm_smul] using hi
  have hm (n : ℕ) : AEStronglyMeasurable (fun x => ‖F n x-f x‖^2) volume :=
    (((hF n).aestronglyMeasurable.sub hf.aestronglyMeasurable).norm.pow 2)
  have hd (n : ℕ) : ∀ᵐ x, ‖‖F n x-f x‖^2‖ ≤ H x := by
    filter_upwards [hFn n,hfn] with x hFx hfx
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    apply pow_le_pow_left₀ (norm_nonneg _) _ 2
    exact (norm_sub_le _ _).trans (by linarith)
  have ht : Tendsto (fun n => ∫ x, ‖F n x-f x‖^2) atTop (𝓝 0) := by
    have hz : ∀ᵐ x, Tendsto (fun n => ‖F n x-f x‖^2) atTop (𝓝 (0:ℝ)) := by
      filter_upwards [hlim] with x hx
      simpa using ((hx.sub (tendsto_const_nhds (x := f x))).norm.pow 2)
    simpa using tendsto_integral_of_dominated_convergence H hm hHi hd hz
  have heq (n : ℕ) : ‖(hF n).toLp (F n)-hf.toLp f‖^2 = ∫ x, ‖F n x-f x‖^2 := by
    rw [spatialL2_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub ((hF n).toLp (F n)) (hf.toLp f),
      (hF n).coeFn_toLp,hf.coeFn_toLp] with x hsub hFx hfx
    simp only [Pi.sub_apply] at hsub
    rw [hsub,hFx,hfx]
  have ht2 : Tendsto (fun n => ‖(hF n).toLp (F n)-hf.toLp f‖^2) atTop (𝓝 0) := by
    simpa only [heq] using ht
  have ht1 := (Real.continuous_sqrt.tendsto 0).comp ht2
  simp only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] at ht1
  exact tendsto_iff_norm_sub_tendsto_zero.mpr ht1

#print axioms configuration_toLp_tendsto_dominated
end TheoremT.Continuum
