import CompactLocalMultiplierLp_v1
import Mathlib.Analysis.Normed.Group.Bounded

noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace TheoremT.Continuum

theorem continuous_memLp_top_on_ball {N : ℕ} {g : Configuration N → ℝ}
    (hg : Continuous g) (R : ℝ) : MemLp g ⊤ (volume.restrict (Metric.ball 0 R)) := by
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : Configuration N) R).exists_bound_of_continuousOn hg.continuousOn
  apply memLp_top_of_bound hg.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
  exact hC x (Metric.ball_subset_closedBall hx)

theorem continuous_ball_multiplier_memLp {N : ℕ} {q : ℝ≥0∞}
    {g : Configuration N → ℝ} (hg : Continuous g) {R : ℝ}
    {f : Configuration N → ℂ} (hf : MemLp f q (volume.restrict (Metric.ball 0 R))) :
    MemLp (fun x => g x • f x) q (volume.restrict (Metric.ball 0 R)) :=
  hf.smul (continuous_memLp_top_on_ball hg R)

#print axioms continuous_memLp_top_on_ball
end TheoremT.Continuum
