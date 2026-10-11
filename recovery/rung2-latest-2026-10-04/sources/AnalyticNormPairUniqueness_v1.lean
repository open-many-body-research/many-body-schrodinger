import AnalyticNormDecompositionUniqueness_v1

/-! Uniqueness of two analytic coefficient pairs representing the same
function on a ball containing the norm singularity. -/
noncomputable section
set_option autoImplicit false
open Set Metric
namespace TheoremT.Continuum
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]

theorem analytic_norm_pair_unique
    {a b c d : E → ℂ} {r : ℝ} (hr : 0<r)
    (ha : AnalyticOnNhd ℝ a (ball 0 r)) (hb : AnalyticOnNhd ℝ b (ball 0 r))
    (hc : AnalyticOnNhd ℝ c (ball 0 r)) (hd : AnalyticOnNhd ℝ d (ball 0 r))
    (hrep : ∀ x ∈ ball 0 r, a x+‖x‖ • b x=c x+‖x‖ • d x) :
    EqOn a c (ball 0 r) ∧ EqOn b d (ball 0 r) := by
  have hz := analytic_norm_decomposition_zero hr (ha.sub hc) (hb.sub hd)
    (fun x hx => by
      have h := hrep x hx
      simp only [Pi.sub_apply,Complex.real_smul] at h ⊢
      linear_combination h)
  exact ⟨fun x hx => sub_eq_zero.mp (hz.1 hx),fun x hx => sub_eq_zero.mp (hz.2 hx)⟩

theorem analytic_norm_pair_unique_with_parameter
    {T : Type*} (U : Set T) (a b c d : E → T → ℂ) {r : ℝ} (hr : 0<r)
    (ha : ∀ t ∈ U, AnalyticOnNhd ℝ (fun x => a x t) (ball 0 r))
    (hb : ∀ t ∈ U, AnalyticOnNhd ℝ (fun x => b x t) (ball 0 r))
    (hc : ∀ t ∈ U, AnalyticOnNhd ℝ (fun x => c x t) (ball 0 r))
    (hd : ∀ t ∈ U, AnalyticOnNhd ℝ (fun x => d x t) (ball 0 r))
    (hrep : ∀ t ∈ U, ∀ x ∈ ball 0 r,
      a x t+‖x‖ • b x t=c x t+‖x‖ • d x t) :
    ∀ t ∈ U, ∀ x ∈ ball 0 r, a x t=c x t ∧ b x t=d x t := by
  intro t ht x hx
  have h := analytic_norm_pair_unique hr (ha t ht) (hb t ht) (hc t ht) (hd t ht) (hrep t ht)
  exact ⟨h.1 hx,h.2 hx⟩

end TheoremT.Continuum
