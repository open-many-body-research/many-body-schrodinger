import FiniteDimSmoothCutoff_v1

/-! A genuine smooth compact extension of a local real distance profile agrees
as a germ at every point of the closed inner box. -/
set_option autoImplicit false
noncomputable section
open Filter Metric
open scoped Topology ContDiff
namespace ManyBody.S8
open TheoremT.Continuum

theorem real_distance_profile_smooth_compact_extension
    {g : (Fin 3 → ℝ) → ℂ} {a : Fin 3 → ℝ} {R : ℝ} (hR : 0<R)
    (hg : ContDiffOn ℝ ∞ g (ball a R)) :
    ∃ G : (Fin 3 → ℝ) → ℂ, ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧
      ∀ q ∈ closedBall a (R/8), G =ᶠ[𝓝 q] g := by
  have hsub : closedBall a (R/8) ⊆ ball a (R/4) := by
    intro q hq
    change dist q a≤R/8 at hq
    change dist q a<R/4
    exact lt_of_le_of_lt hq (by linarith)
  obtain ⟨χ,hχ,hc,hs,h1⟩ := finiteDim_compact_exists_smooth_cutoff
    (isCompact_closedBall a (R/8)) isOpen_ball hsub
  let G : (Fin 3 → ℝ) → ℂ := fun q => χ q • g q
  have hG : ContDiff ℝ ∞ G := by
    rw [contDiff_iff_contDiffAt]
    intro q
    by_cases hq : q ∈ tsupport χ
    · have hsmall : dist q a<R/4 := hs hq
      have hfull : q ∈ ball a R := lt_trans hsmall (by linarith)
      exact hχ.contDiffAt.smul (hg.contDiffAt (isOpen_ball.mem_nhds hfull))
    · have hz : G =ᶠ[𝓝 q] fun _ => 0 := by
        filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hq] with x hx
        simp [G,image_eq_zero_of_notMem_tsupport hx]
      exact contDiffAt_const.congr_of_eventuallyEq hz
  refine ⟨G,hG,hc.smul_right,?_⟩
  intro q hq
  filter_upwards [h1 q hq] with x hx
  simp [G,hx]

#print axioms real_distance_profile_smooth_compact_extension
end ManyBody.S8
