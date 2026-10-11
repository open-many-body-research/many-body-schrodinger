import SmoothCutoffRescaleBalls_v1
import SmoothCutoffRescaleDerivatives_v1

/-! One supplied base cutoff yields a translated family with exact support,
plateau, and scale-dependent derivative constants. The base cutoff and its
actual operator-norm bounds remain explicit inputs, not computed numeric data. -/
noncomputable section
open scoped Topology ContDiff
namespace TheoremT.Continuum
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem cutoffRescale_quantitative_family
    {η : E → ℝ} (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    {Rin Rout M L1 L2 : ℝ}
    (hs : tsupport η ⊆ Metric.closedBall (0 : E) Rout)
    (hp : ∀ x ∈ Metric.closedBall (0 : E) Rin, η x = 1)
    (hM : ∀ x, |η x| ≤ M)
    (hL1 : ∀ x, ‖fderiv ℝ η x‖ ≤ L1)
    (hL2 : ∀ x, ‖fderiv ℝ (fderiv ℝ η) x‖ ≤ L2)
    (a : E) {r : ℝ} (hr : 0 < r) :
    ContDiff ℝ ∞ (cutoffRescale η a r) ∧
    HasCompactSupport (cutoffRescale η a r) ∧
    tsupport (cutoffRescale η a r) ⊆ Metric.closedBall a (r*Rout) ∧
    (∀ x ∈ Metric.closedBall a (r*Rin), cutoffRescale η a r x = 1) ∧
    (∀ x, |cutoffRescale η a r x| ≤ M) ∧
    (∀ x v, |fderiv ℝ (cutoffRescale η a r) x v| ≤ (L1/r)*‖v‖) ∧
    ∀ x v w, |fderiv ℝ (fun y => fderiv ℝ (cutoffRescale η a r) y v) x w| ≤
      (L2/r^2)*‖v‖*‖w‖ :=
  ⟨cutoffRescale_contDiff hη a r,cutoffRescale_hasCompactSupport hcη a hr.ne',
    cutoffRescale_tsupport_closedBall hs a hr,cutoffRescale_plateau_closedBall hp a hr,
    cutoffRescale_value_bound hM a r,cutoffRescale_first_bound hη hL1 a hr,
    cutoffRescale_second_bound hη hL2 a hr⟩

end TheoremT.Continuum
