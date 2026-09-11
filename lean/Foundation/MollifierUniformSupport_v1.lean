import HardyMollifierStrongRepresentation_v1
import HardyLaplacianCore_v2

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace TheoremT.Continuum

theorem mollifierKernel_eq_zero_of_two_lt_norm {N n : ℕ} {x : Configuration N}
    (hx : 2 < ‖x‖) : mollifierKernel N n x=0 := by
  have hr : (mollifierBump N n).rOut ≤ 2 := by
    dsimp [mollifierBump]
    have h : ((n:ℝ)+1)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
    linarith
  have hn : x ∉ Function.support (mollifierKernel N n) := by
    rw [mollifierKernel,(mollifierBump N n).support_normed_eq]
    simpa only [mem_ball_zero_iff,not_lt] using (hr.trans hx.le)
  simpa only [Function.mem_support,not_not] using hn

theorem mollify_eq_zero_outside_of_ae_support {N : ℕ} {R : ℝ} {f : SpatialL2 N}
    (hs : ∀ᵐ y ∂volume, R < ‖y‖ → f y=0) (n : ℕ) {x : Configuration N}
    (hx : R+2 < ‖x‖) : mollify (mollifierKernel N n) f x=0 := by
  unfold mollify
  apply integral_eq_zero_of_ae
  filter_upwards [hs] with y hy
  by_cases h : R < ‖y‖
  · simp only [hy h,smul_zero,Pi.zero_apply]
  · have hb : 2 < ‖x-y‖ := by
      have he : ‖x‖ ≤ ‖x-y‖+‖y‖ := by simpa using norm_add_le (x-y) y
      push_neg at h
      linarith
    simp only [mollifierKernel_eq_zero_of_two_lt_norm hb,zero_smul,Pi.zero_apply]

theorem mollify_tsupport_subset_closedBall {N : ℕ} {R : ℝ} {f : SpatialL2 N}
    (hs : ∀ᵐ y ∂volume, R < ‖y‖ → f y=0) (n : ℕ) :
    tsupport (mollify (mollifierKernel N n) f) ⊆ Metric.closedBall 0 (R+2) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  rw [mem_closedBall_zero_iff]
  by_contra hn
  exact hx (mollify_eq_zero_outside_of_ae_support hs n (lt_of_not_ge hn))

theorem smoothLaplacian_eq_zero_outside_tsupport {N : ℕ} (φ : Configuration N → ℂ)
    {x : Configuration N} (hx : x ∉ tsupport φ) : smoothLaplacian φ x=0 := by
  apply Finset.sum_eq_zero
  intro k hk
  apply image_eq_zero_of_notMem_tsupport
  intro hm
  exact hx ((tsupport_fderiv_apply_subset ℝ (coordinateVector k))
    ((tsupport_fderiv_apply_subset ℝ (coordinateVector k)) hm))

#print axioms mollify_tsupport_subset_closedBall
#print axioms smoothLaplacian_eq_zero_outside_tsupport
end TheoremT.Continuum
