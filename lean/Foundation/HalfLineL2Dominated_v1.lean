import HalfLineCompactPairing_v1
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace
namespace TheoremT.HalfLine

theorem l2_norm_sq_integral (f : E) : ‖f‖^2 = ∫ r, ‖f r‖^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

theorem tendsto_toLp_of_dominated {F : ℕ → ℝ → ℂ} {f : ℝ → ℂ} {bound : ℝ → ℝ}
    (hF : ∀ n, MemLp (F n) 2 μ) (hf : MemLp f 2 μ) (hb : MemLp bound 2 μ)
    (hFn : ∀ n, ∀ᵐ r ∂μ, ‖F n r‖ ≤ ‖bound r‖)
    (hfn : ∀ᵐ r ∂μ, ‖f r‖ ≤ ‖bound r‖)
    (hlim : ∀ᵐ r ∂μ, Tendsto (fun n => F n r) atTop (𝓝 (f r))) :
    Tendsto (fun n => (hF n).toLp (F n)) atTop (𝓝 (hf.toLp f)) := by
  let H : ℝ → ℝ := fun r => (2*‖bound r‖)^2
  have hHi : Integrable H μ := by
    have hi := (hb.const_smul (2:ℝ)).integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)
    simpa [H, norm_smul] using hi
  have hm (n : ℕ) : AEStronglyMeasurable (fun r => ‖F n r-f r‖^2) μ :=
    (((hF n).aestronglyMeasurable.sub hf.aestronglyMeasurable).norm.pow 2)
  have hd (n : ℕ) : ∀ᵐ r ∂μ, ‖‖F n r-f r‖^2‖ ≤ H r := by
    filter_upwards [hFn n,hfn] with r hFr hfr
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    apply pow_le_pow_left₀ (norm_nonneg _) _ 2
    exact (norm_sub_le _ _).trans (by linarith)
  have ht : Tendsto (fun n => ∫ r, ‖F n r-f r‖^2 ∂μ) atTop (𝓝 0) := by
    have hz : ∀ᵐ r ∂μ, Tendsto (fun n => ‖F n r-f r‖^2) atTop (𝓝 (0:ℝ)) := by
      filter_upwards [hlim] with r hr
      simpa using ((hr.sub (tendsto_const_nhds (x := f r))).norm.pow 2)
    simpa using tendsto_integral_of_dominated_convergence H hm hHi hd hz
  have heq (n : ℕ) : ‖(hF n).toLp (F n)-hf.toLp f‖^2 =
      ∫ r, ‖F n r-f r‖^2 ∂μ := by
    rw [l2_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub ((hF n).toLp (F n)) (hf.toLp f),
      (hF n).coeFn_toLp, hf.coeFn_toLp] with r hsub hFr hfr
    simp only [Pi.sub_apply] at hsub
    rw [hsub,hFr,hfr]
  have ht2 : Tendsto (fun n => ‖(hF n).toLp (F n)-hf.toLp f‖^2) atTop (𝓝 0) := by
    simpa only [heq] using ht
  have ht1 := (Real.continuous_sqrt.tendsto 0).comp ht2
  simp only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] at ht1
  exact tendsto_iff_norm_sub_tendsto_zero.mpr ht1

#print axioms tendsto_toLp_of_dominated
end TheoremT.HalfLine
