import HardyMollifierStrongRepresentation_v1
import Mathlib.Topology.Order.LiminfLimsup

/-! Strong L² convergence from a.e. convergence and norm contraction, followed
by its application to the actual normalized continuum mollifier sequence. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace TheoremT.HardyLimit

private theorem l2_norm_sq_integral {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (f : Lp ℂ 2 μ) : ‖f‖^2 = ∫ x, ‖f x‖^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

/-- Fatou lower semicontinuity of the actual L² norm under a.e. convergence. -/
theorem l2_norm_sq_le_liminf_of_ae_tendsto {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (F : ℕ → Lp ℂ 2 μ) (f : Lp ℂ 2 μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    ENNReal.ofReal (‖f‖^2) ≤ liminf (fun n => ENNReal.ofReal (‖F n‖^2)) atTop := by
  have hi (g : Lp ℂ 2 μ) : Integrable (fun x => ‖g x‖^2) μ :=
    (Lp.memLp g).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have he (g : Lp ℂ 2 μ) :
      ENNReal.ofReal (‖g‖^2) = ∫⁻ x, ENNReal.ofReal (‖g x‖^2) ∂μ := by
    rw [l2_norm_sq_integral]
    exact ofReal_integral_eq_lintegral_ofReal (hi g) (ae_of_all _ (fun x => sq_nonneg _))
  rw [he f]
  calc
    (∫⁻ x, ENNReal.ofReal (‖f x‖^2) ∂μ) =
        ∫⁻ x, liminf (fun n => ENNReal.ofReal (‖F n x‖^2)) atTop ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hlim] with x hx
      exact ((ENNReal.continuous_ofReal.tendsto _).comp (hx.norm.pow 2)).liminf_eq.symm
    _ ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal (‖F n x‖^2) ∂μ) atTop :=
      lintegral_liminf_le' (fun n => (hi (F n)).aemeasurable.ennreal_ofReal)
    _ = liminf (fun n => ENNReal.ofReal (‖F n‖^2)) atTop := by simp only [← he]

/-- A.e. convergence and a uniform contraction toward the target norm imply
strong convergence in L², without any finite-measure hypothesis. -/
theorem l2_tendsto_of_ae_tendsto_norm_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (F : ℕ → Lp ℂ 2 μ) (f : Lp ℂ 2 μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    (hb : ∀ n, ‖F n‖ ≤ ‖f‖) : Tendsto F atTop (𝓝 f) := by
  have hsumlim : ∀ᵐ x ∂μ,
      Tendsto (fun n => (F n + f) x) atTop (𝓝 ((f + f) x)) := by
    have hs : ∀ᵐ x ∂μ, ∀ n : ℕ, (F n + f) x = F n x + f x := by
      rw [ae_all_iff]
      intro n
      exact Lp.coeFn_add (F n) f
    filter_upwards [hs, Lp.coeFn_add f f, hlim] with x hx hxx hxlim
    simpa only [hx, hxx, Pi.add_apply] using hxlim.add_const (f x)
  have htarget : ‖f + f‖^2 = 4 * ‖f‖^2 := by
    rw [← two_smul ℝ f, norm_smul]
    norm_num
    ring
  have hlow := l2_norm_sq_le_liminf_of_ae_tendsto (fun n => F n + f) (f + f) hsumlim
  rw [htarget] at hlow
  have hupper (n : ℕ) : ‖F n + f‖^2 ≤ 4 * ‖f‖^2 := by
    have h := norm_add_le (F n) f
    have hbn := hb n
    nlinarith [norm_nonneg (F n + f), norm_nonneg f]
  have hsumENN : Tendsto (fun n => ENNReal.ofReal (‖F n + f‖^2)) atTop
      (𝓝 (ENNReal.ofReal (4 * ‖f‖^2))) := by
    apply tendsto_of_le_liminf_of_limsup_le hlow
    apply limsup_le_of_le
    · isBoundedDefault
    · exact Eventually.of_forall (fun n => ENNReal.ofReal_le_ofReal (hupper n))
    all_goals isBoundedDefault
  have hsum : Tendsto (fun n => ‖F n + f‖^2) atTop (𝓝 (4 * ‖f‖^2)) := by
    have h := (ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp hsumENN
    change Tendsto (fun n => (ENNReal.ofReal (‖F n + f‖^2)).toReal) atTop
      (𝓝 ((ENNReal.ofReal (4 * ‖f‖^2)).toReal)) at h
    simpa only [ENNReal.toReal_ofReal (sq_nonneg _),
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 4 * ‖f‖^2)] using h
  have hdiff (n : ℕ) : ‖F n - f‖^2 ≤ 4 * ‖f‖^2 - ‖F n + f‖^2 := by
    have hp := parallelogram_law_with_norm ℂ (F n) f
    have hbn := hb n
    nlinarith [norm_nonneg (F n), norm_nonneg f]
  have hsq : Tendsto (fun n => ‖F n - f‖^2) atTop (𝓝 0) := by
    have ht : Tendsto (fun n => 4 * ‖f‖^2 - ‖F n + f‖^2) atTop
        (𝓝 (4 * ‖f‖^2 - 4 * ‖f‖^2)) := tendsto_const_nhds.sub hsum
    have ht' : Tendsto (fun n => 4 * ‖f‖^2 - ‖F n + f‖^2) atTop (𝓝 0) := by
      simpa only [sub_self] using ht
    exact squeeze_zero (fun n => sq_nonneg _) hdiff ht'
  have hn : Tendsto (fun n => ‖F n - f‖) atTop (𝓝 0) := by
    simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hsq.sqrt
  exact tendsto_iff_dist_tendsto_zero.mpr (by simpa only [dist_eq_norm] using hn)

#print axioms l2_norm_sq_le_liminf_of_ae_tendsto
#print axioms l2_tendsto_of_ae_tendsto_norm_le
end TheoremT.HardyLimit

namespace TheoremT.Continuum
/-- The actual normalized shrinking mollifiers converge strongly in continuum L². -/
theorem mollifyLp_tendsto {N : ℕ} (f : SpatialL2 N) :
    Tendsto (fun n : ℕ => mollifyLp n f) atTop (𝓝 f) :=
  TheoremT.HardyLimit.l2_tendsto_of_ae_tendsto_norm_le _ _
    (mollifyLp_ae_tendsto f) (fun n => mollifyLp_norm_le n f)

set_option pp.proofs false in
#print mollifyLp_tendsto
#print axioms mollifyLp_tendsto
end TheoremT.Continuum
