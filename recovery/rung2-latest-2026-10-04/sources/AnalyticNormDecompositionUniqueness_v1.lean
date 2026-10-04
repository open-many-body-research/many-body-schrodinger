import AnalyticAbsoluteValueDecomposition_v1

/-! Uniqueness of analytic-plus-norm decompositions on a real ball in a
nontrivial normed vector space. The radial-line argument includes the
center; no analytic regularity of the norm is assumed. -/
noncomputable section
set_option autoImplicit false
open Set Metric
namespace TheoremT.Continuum
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem analytic_norm_decomposition_zero_along_line
    {f g : E → ℂ} {r : ℝ} (hr : 0<r)
    (hf : AnalyticOnNhd ℝ f (ball 0 r)) (hg : AnalyticOnNhd ℝ g (ball 0 r))
    (hfg : ∀ x ∈ ball 0 r, f x + ‖x‖ • g x=0)
    (v : E) (hv : v≠0) :
    ∀ t ∈ Ioo (-(r/‖v‖)) (r/‖v‖), f (t • v)=0 ∧ g (t • v)=0 := by
  have hvnorm : 0<‖v‖ := norm_pos_iff.mpr hv
  have hmap : MapsTo (fun t : ℝ => t • v) (Ioo (-(r/‖v‖)) (r/‖v‖)) (ball 0 r) := by
    intro t ht
    rw [mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs]
    exact (lt_div_iff₀ hvnorm).mp (abs_lt.mpr ht)
  have hff : AnalyticOnNhd ℝ (fun t : ℝ => f (t • v)) (Ioo (-(r/‖v‖)) (r/‖v‖)) := by
    intro t ht
    exact (hf (t • v) (hmap ht)).comp (f := fun u : ℝ => u • v)
      ((ContinuousLinearMap.toSpanSingleton ℝ v).analyticAt t)
  have hgg : AnalyticOnNhd ℝ (fun t : ℝ => ‖v‖ • g (t • v))
      (Ioo (-(r/‖v‖)) (r/‖v‖)) := by
    intro t ht
    exact ((hg (t • v) (hmap ht)).comp (f := fun u : ℝ => u • v)
      ((ContinuousLinearMap.toSpanSingleton ℝ v).analyticAt t)).const_smul (c := ‖v‖)
  have hzero := analytic_absolute_value_decomposition_zero (div_pos hr hvnorm) hff hgg
    (fun t ht => by simpa only [norm_smul,Real.norm_eq_abs,mul_smul] using hfg (t • v) (hmap ht))
  intro t ht
  refine ⟨hzero.1 ht,?_⟩
  have h : ‖v‖ • g (t • v)=0 := hzero.2 ht
  exact (smul_eq_zero.mp h).resolve_left hvnorm.ne'

theorem analytic_norm_decomposition_zero [Nontrivial E]
    {f g : E → ℂ} {r : ℝ} (hr : 0<r)
    (hf : AnalyticOnNhd ℝ f (ball 0 r)) (hg : AnalyticOnNhd ℝ g (ball 0 r))
    (hfg : ∀ x ∈ ball 0 r, f x + ‖x‖ • g x=0) :
    EqOn f 0 (ball 0 r) ∧ EqOn g 0 (ball 0 r) := by
  have hpoint (x : E) (hx : x ∈ ball 0 r) : f x=0 ∧ g x=0 := by
    by_cases hx0 : x=0
    · obtain ⟨v,hv⟩ := exists_ne (0 : E)
      have hs : 0<r/‖v‖ := div_pos hr (norm_pos_iff.mpr hv)
      have h := analytic_norm_decomposition_zero_along_line hr hf hg hfg v hv 0
        ⟨by linarith,hs⟩
      simpa only [zero_smul,hx0] using h
    · have hn : ‖x‖<r := by simpa only [mem_ball,dist_zero_right] using hx
      have hs : 1<r/‖x‖ := (lt_div_iff₀ (norm_pos_iff.mpr hx0)).mpr (by simpa using hn)
      have h := analytic_norm_decomposition_zero_along_line hr hf hg hfg x hx0 1
        ⟨by linarith,hs⟩
      simpa only [one_smul] using h
  exact ⟨fun x hx => (hpoint x hx).1,fun x hx => (hpoint x hx).2⟩

end TheoremT.Continuum
