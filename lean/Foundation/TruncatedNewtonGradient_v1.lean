import NewtonComplexGradientRepresentation_v1
import MollifierUniformSupport_v1

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace TheoremT.Continuum

def truncatedNewtonGradient (N : ℕ) (k : Coordinate N) (R : ℝ) : Configuration N → ℝ :=
  (Metric.closedBall 0 R).indicator (normalizedNewtonGradient N k)

theorem truncatedNewtonGradient_measurable (N : ℕ) (k : Coordinate N) (R : ℝ) :
    Measurable (truncatedNewtonGradient N k R) := by
  exact (measurable_const.mul (newtonGradient_measurable N k)).indicator Metric.isClosed_closedBall.measurableSet

theorem truncatedNewtonGradient_integrable {N : ℕ} (hN : 0 < N) (k : Coordinate N) (R : ℝ) :
    Integrable (truncatedNewtonGradient N k R) := by
  apply memLp_one_iff_integrable.mp
  simpa only [ENNReal.ofReal_one,truncatedNewtonGradient] using normalizedNewtonGradient_indicator_memLp hN k
    (q := 1) (by norm_num) (by linarith) R

theorem truncatedNewtonGradient_memLp {N : ℕ} (hN : 0 < N) (k : Coordinate N) (R : ℝ)
    {q : ℝ} (hq : 0 < q) (hqd : ((3*N:ℝ)-1)*q < (3*N:ℝ)) :
    MemLp (truncatedNewtonGradient N k R) (ENNReal.ofReal q) volume :=
  normalizedNewtonGradient_indicator_memLp hN k hq hqd R

theorem truncated_newton_gradient_smooth_representation {N : ℕ} (hN : 0 < N)
    {φ : Configuration N → ℂ} (hφ : ContDiff ℝ ∞ φ) {R A : ℝ}
    (hs : tsupport φ ⊆ Metric.closedBall 0 R) (x : Configuration N) (hx : ‖x‖ ≤ A)
    (k : Coordinate N) :
    (∫ y, truncatedNewtonGradient N k (A+R) y • smoothLaplacian φ (x-y))=smoothPartial φ k x := by
  have hc : HasCompactSupport φ := (isCompact_closedBall 0 R).of_isClosed_subset (isClosed_tsupport φ) hs
  rw [← smooth_compact_complex_newton_gradient_representation hN hφ hc x k]
  apply integral_congr_ae
  filter_upwards with y
  by_cases hy : y ∈ Metric.closedBall (0 : Configuration N) (A+R)
  · simp only [truncatedNewtonGradient,Set.indicator_of_mem hy]
  · have hn : A+R < ‖y‖ := by simpa only [mem_closedBall_zero_iff,not_le] using hy
    have hnot : x-y ∉ tsupport φ := by
      intro hm
      have hb : ‖x-y‖ ≤ R := by simpa only [mem_closedBall_zero_iff] using hs hm
      have ht : ‖y‖ ≤ ‖x‖+‖x-y‖ := by
        have ht := norm_sub_le x (x-y)
        simpa only [sub_sub_cancel] using ht
      linarith
    simp only [truncatedNewtonGradient,Set.indicator_of_notMem hy,zero_smul,
      smoothLaplacian_eq_zero_outside_tsupport φ hnot,smul_zero]

#print axioms truncated_newton_gradient_smooth_representation
end TheoremT.Continuum
