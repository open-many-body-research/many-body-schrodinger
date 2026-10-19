import AnalyticNormPairUniqueness_v1

/-! The analytic coefficients inherit every linear isometry symmetry of
the represented function on a collision-centered ball. -/
noncomputable section
set_option autoImplicit false
open Set Metric
namespace TheoremT.Continuum
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]

theorem analytic_norm_coefficients_isometry_invariant
    {a b u : E → ℂ} {r : ℝ} (hr : 0<r)
    (ha : AnalyticOnNhd ℝ a (ball 0 r)) (hb : AnalyticOnNhd ℝ b (ball 0 r))
    (hrep : ∀ x ∈ ball 0 r, u x=a x+‖x‖ • b x)
    (R : E ≃ₗᵢ[ℝ] E) (hu : ∀ x ∈ ball 0 r, u (R x)=u x) :
    EqOn (a ∘ R) a (ball 0 r) ∧ EqOn (b ∘ R) b (ball 0 r) := by
  have hm (x : E) (hx : x ∈ ball 0 r) : R x ∈ ball 0 r := by
    simpa only [mem_ball,dist_zero_right,R.norm_map] using hx
  have haR : AnalyticOnNhd ℝ (a ∘ R) (ball 0 r) := by
    intro x hx
    exact (ha (R x) (hm x hx)).comp (f := fun y => R y) (R.toContinuousLinearEquiv.analyticAt x)
  have hbR : AnalyticOnNhd ℝ (b ∘ R) (ball 0 r) := by
    intro x hx
    exact (hb (R x) (hm x hx)).comp (f := fun y => R y) (R.toContinuousLinearEquiv.analyticAt x)
  apply analytic_norm_pair_unique hr haR hbR ha hb
  intro x hx
  have h := (hrep (R x) (hm x hx)).symm.trans ((hu x hx).trans (hrep x hx))
  simpa only [Function.comp_apply,R.norm_map] using h

end TheoremT.Continuum
