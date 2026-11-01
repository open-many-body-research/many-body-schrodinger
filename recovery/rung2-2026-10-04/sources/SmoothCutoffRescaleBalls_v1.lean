import SmoothCutoffRescaleGeometry_v1

/-! Exact ball/closed-ball transport and pointwise plateau/value bounds under
positive scalar rescaling, in the selected norm on the actual source space. -/
noncomputable section
namespace TheoremT.Continuum
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem cutoffRescaleMap_norm (a : E) {r : ℝ} (hr : 0 < r) (x : E) :
    ‖cutoffRescaleMap a r x‖ = r⁻¹*‖x-a‖ := by
  simp only [cutoffRescaleMap,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]

theorem cutoffRescale_closedBall_image (a : E) {r : ℝ} (hr : 0 < r) (R : ℝ) :
    (fun y => a+r • y) '' Metric.closedBall (0 : E) R = Metric.closedBall a (r*R) := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    have hyn : ‖y‖ ≤ R := by simpa only [Metric.mem_closedBall,dist_zero_right] using hy
    rw [Metric.mem_closedBall,dist_eq_norm]
    simpa only [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hr] using
      mul_le_mul_of_nonneg_left hyn hr.le
  · intro hx
    have hxn : ‖x-a‖ ≤ r*R := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hx
    refine ⟨cutoffRescaleMap a r x,?_,cutoffRescaleMap_inverse_left a hr.ne' x⟩
    rw [Metric.mem_closedBall,dist_zero_right,cutoffRescaleMap_norm a hr]
    calc
      _ ≤ r⁻¹*(r*R) := mul_le_mul_of_nonneg_left hxn (inv_nonneg.mpr hr.le)
      _ = R := by rw [← mul_assoc,inv_mul_cancel₀ hr.ne',one_mul]

theorem cutoffRescale_ball_image (a : E) {r : ℝ} (hr : 0 < r) (R : ℝ) :
    (fun y => a+r • y) '' Metric.ball (0 : E) R = Metric.ball a (r*R) := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    have hyn : ‖y‖ < R := by simpa only [Metric.mem_ball,dist_zero_right] using hy
    rw [Metric.mem_ball,dist_eq_norm]
    simpa only [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hr] using
      mul_lt_mul_of_pos_left hyn hr
  · intro hx
    have hxn : ‖x-a‖ < r*R := by simpa only [Metric.mem_ball,dist_eq_norm] using hx
    refine ⟨cutoffRescaleMap a r x,?_,cutoffRescaleMap_inverse_left a hr.ne' x⟩
    rw [Metric.mem_ball,dist_zero_right,cutoffRescaleMap_norm a hr]
    calc
      _ < r⁻¹*(r*R) := mul_lt_mul_of_pos_left hxn (inv_pos.mpr hr)
      _ = R := by rw [← mul_assoc,inv_mul_cancel₀ hr.ne',one_mul]

theorem cutoffRescale_plateau_closedBall {η : E → ℝ} {R : ℝ}
    (hη : ∀ x ∈ Metric.closedBall (0 : E) R, η x = 1) (a : E) {r : ℝ} (hr : 0 < r) :
    ∀ x ∈ Metric.closedBall a (r*R), cutoffRescale η a r x = 1 := by
  rw [← cutoffRescale_closedBall_image a hr R]
  exact cutoffRescale_plateau_image hη a hr.ne'

theorem cutoffRescale_plateau_ball {η : E → ℝ} {R : ℝ}
    (hη : ∀ x ∈ Metric.ball (0 : E) R, η x = 1) (a : E) {r : ℝ} (hr : 0 < r) :
    ∀ x ∈ Metric.ball a (r*R), cutoffRescale η a r x = 1 := by
  rw [← cutoffRescale_ball_image a hr R]
  exact cutoffRescale_plateau_image hη a hr.ne'

theorem cutoffRescale_value_bound {η : E → ℝ} {M : ℝ}
    (hM : ∀ x, |η x| ≤ M) (a : E) (r : ℝ) (x : E) : |cutoffRescale η a r x| ≤ M :=
  hM (cutoffRescaleMap a r x)

end TheoremT.Continuum
