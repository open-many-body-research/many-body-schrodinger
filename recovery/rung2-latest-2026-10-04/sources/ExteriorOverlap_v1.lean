import CutoffConvergence_v2
import PuncturedCutoffGeometry_v1

/-! Localization of an actual L² overlap outside a sufficiently large ball.
The conclusion is uniform over every exterior vector; the radius is an existence
result, not an implemented radius-selection algorithm. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace TheoremT.Continuum

theorem cutoffAt_inner_zero_of_exterior {N : ℕ} (g v : SpatialL2 N) (n : ℕ)
    (hv : ∀ᵐ x, ‖x‖ ≤ 2*((n : ℝ)+1) → v x = 0) :
    inner ℂ (cutoffAt n g) v = 0 := by
  rw [L2.inner_def]
  have he : (fun x => inner ℂ (cutoffAt n g x) (v x)) =ᵐ[volume] (fun _ => 0) := by
    filter_upwards [cutoffAt_ae n g,hv] with x hx hvx
    by_cases hr : ‖x‖ ≤ 2*((n : ℝ)+1)
    · rw [hvx hr,inner_zero_right]
    · rw [hx,scaledCutoff_eq_zero_of_two_mul_le (by positivity) (le_of_not_ge hr),
        zero_smul,inner_zero_left]
  rw [integral_congr_ae he,integral_zero]

theorem exists_radius_exterior_overlap_small {N : ℕ} (g : SpatialL2 N)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ v : SpatialL2 N,
      (∀ᵐ x, ‖x‖ ≤ R → v x = 0) → ‖inner ℂ g v‖ ≤ ε * ‖v‖ := by
  have ht : Tendsto (fun n : ℕ => ‖g - cutoffAt n g‖) atTop (𝓝 0) := by
    simpa only [sub_self,norm_zero] using
      ((tendsto_const_nhds (x := g)).sub (cutoffAt_tendsto g)).norm
  have he := ht.eventually (gt_mem_nhds hε)
  obtain ⟨n,hn⟩ := he.exists
  refine ⟨2*((n : ℝ)+1),by positivity,fun v hv => ?_⟩
  have hzero := cutoffAt_inner_zero_of_exterior g v n hv
  have heq : inner ℂ g v = inner ℂ (g-cutoffAt n g) v := by
    rw [inner_sub_left,hzero,sub_zero]
  rw [heq]
  exact (norm_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right hn.le (norm_nonneg v))

#print axioms cutoffAt_inner_zero_of_exterior
#print axioms exists_radius_exterior_overlap_small
end TheoremT.Continuum
