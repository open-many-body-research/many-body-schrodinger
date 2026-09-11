import PuncturedCutoffGeometry_v1
import ConstantOpenDerivative_v1

noncomputable section
open MeasureTheory
namespace TheoremT.Continuum

theorem scaledCutoff_tsupport_subset_closedBall {N : ℕ} {A : ℝ} (hA : 0 < A) :
    tsupport (scaledCutoff N A) ⊆ Metric.closedBall 0 (2*A) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  rw [mem_closedBall_zero_iff]
  by_contra hn
  exact hx (scaledCutoff_eq_zero_of_two_mul_le hA (lt_of_not_ge hn).le)

theorem scaledCutoff_tsupport_subset_four_ball {N : ℕ} {A : ℝ} (hA : 0 < A) :
    tsupport (scaledCutoff N A) ⊆ Metric.ball 0 (4*A) := by
  intro x hx
  have ht : ‖x‖ ≤ 2*A := by
    simpa only [mem_closedBall_zero_iff] using scaledCutoff_tsupport_subset_closedBall hA hx
  rw [mem_ball_zero_iff]
  linarith

theorem scaledCutoff_fderiv_zero_on_inner_ball {N : ℕ} {A : ℝ} (hA : 0 < A)
    {x : Configuration N} (hx : x ∈ Metric.ball 0 A) : fderiv ℝ (scaledCutoff N A) x=0 :=
  fderiv_zero_of_constant_open Metric.isOpen_ball
    (fun y hy => scaledCutoff_eq_one hA (mem_ball_zero_iff.mp hy).le) hx

#print axioms scaledCutoff_tsupport_subset_four_ball
#print axioms scaledCutoff_fderiv_zero_on_inner_ball
end TheoremT.Continuum
