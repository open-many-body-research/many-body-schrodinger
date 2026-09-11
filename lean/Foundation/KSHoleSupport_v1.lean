import KSHoleDerivatives_v1
import Mathlib.Analysis.Calculus.FDeriv.Congr

noncomputable section
open Filter
open scoped Topology ContDiff
namespace TheoremT.Continuum

theorem locally_constant_first_second_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℝ} {x : E} {c : ℝ}
    (h : f =ᶠ[𝓝 x] fun _ => c) (v w : E) :
    fderiv ℝ f x v = 0 ∧ fderiv ℝ (fun y => fderiv ℝ f y v) x w = 0 := by
  have he : (fun y => fderiv ℝ f y v) =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
    simp [hy]
  constructor
  · simpa using congrArg (fun L => L v) (h.fderiv_eq (𝕜 := ℝ))
  · simpa using congrArg (fun L => L w) (he.fderiv_eq (𝕜 := ℝ))

theorem ksHole_jet_zero_outer {δ : ℝ} (hδ : 0 < δ) {x : KSSpace}
    (hx : 2*δ < ‖x‖) (v w : KSSpace) :
    fderiv ℝ (ksHole δ) x v=0 ∧
    fderiv ℝ (fun y => fderiv ℝ (ksHole δ) y v) x w=0 := by
  apply locally_constant_first_second_zero (c := 1)
  filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with y hy
  exact ksHole_one_on_outer hδ hy.le

theorem ksHole_jet_zero_inner {δ : ℝ} (hδ : 0 < δ) {x : KSSpace}
    (hx : ‖x‖ < δ) (v w : KSSpace) :
    fderiv ℝ (ksHole δ) x v=0 ∧
    fderiv ℝ (fun y => fderiv ℝ (ksHole δ) y v) x w=0 := by
  apply locally_constant_first_second_zero (c := 0)
  filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with y hy
  exact ksHole_zero_on_inner hδ hy.le

theorem ksHole_derivative_tsupport {δ : ℝ} (hδ : 0 < δ) (v : KSSpace) :
    tsupport (fun x => fderiv ℝ (ksHole δ) x v) ⊆ Metric.closedBall 0 (2*δ) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  by_contra hn
  have ho : 2*δ < ‖x‖ := by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hn
  exact hx (ksHole_jet_zero_outer hδ ho v 0).1

theorem ksHole_secondDerivative_tsupport {δ : ℝ} (hδ : 0 < δ) (v w : KSSpace) :
    tsupport (fun x => fderiv ℝ (fun y => fderiv ℝ (ksHole δ) y v) x w) ⊆
      Metric.closedBall 0 (2*δ) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  by_contra hn
  have ho : 2*δ < ‖x‖ := by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hn
  exact hx (ksHole_jet_zero_outer hδ ho v w).2

#print axioms ksHole_derivative_tsupport
#print axioms ksHole_secondDerivative_tsupport
end TheoremT.Continuum
