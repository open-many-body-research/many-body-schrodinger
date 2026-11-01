import FiniteDimSmoothCutoff_v1

/-! Affine translation and scalar rescaling of a supplied smooth cutoff in
its actual finite-dimensional real normed space. This applies equally to an
ordinary product maximum norm or its Euclidean copy, without identifying them.
No particular base cutoff or computed numerical derivative bound is assumed. -/
noncomputable section
open scoped Topology ContDiff
namespace TheoremT.Continuum
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def cutoffRescaleMap (a : E) (r : ℝ) (x : E) : E := r⁻¹ • (x-a)

def cutoffRescale (η : E → ℝ) (a : E) (r : ℝ) (x : E) : ℝ := η (cutoffRescaleMap a r x)

theorem cutoffRescaleMap_contDiff (a : E) (r : ℝ) : ContDiff ℝ ∞ (cutoffRescaleMap a r) := by
  unfold cutoffRescaleMap
  fun_prop

theorem cutoffRescale_contDiff {η : E → ℝ} (hη : ContDiff ℝ ∞ η) (a : E) (r : ℝ) :
    ContDiff ℝ ∞ (cutoffRescale η a r) := hη.comp (cutoffRescaleMap_contDiff a r)

theorem cutoffRescaleMap_inverse_left (a : E) {r : ℝ} (hr : r ≠ 0) (x : E) :
    a+r • cutoffRescaleMap a r x = x := by
  rw [cutoffRescaleMap,smul_smul,mul_inv_cancel₀ hr,one_smul]
  abel

theorem cutoffRescaleMap_inverse_right (a : E) {r : ℝ} (hr : r ≠ 0) (x : E) :
    cutoffRescaleMap a r (a+r • x) = x := by
  simp only [cutoffRescaleMap,add_sub_cancel_left,smul_smul,inv_mul_cancel₀ hr,one_smul]

def cutoffRescaleHomeomorph (a : E) (r : ℝ) (hr : r ≠ 0) : E ≃ₜ E where
  toEquiv := {
    toFun := cutoffRescaleMap a r
    invFun := fun x => a+r • x
    left_inv := cutoffRescaleMap_inverse_left a hr
    right_inv := cutoffRescaleMap_inverse_right a hr }
  continuous_toFun := (cutoffRescaleMap_contDiff a r).continuous
  continuous_invFun := by fun_prop

theorem cutoffRescale_tsupport_preimage (η : E → ℝ) (a : E) {r : ℝ} (hr : r ≠ 0) :
    tsupport (cutoffRescale η a r) = (cutoffRescaleMap a r) ⁻¹' tsupport η :=
  tsupport_comp_eq_preimage η (cutoffRescaleHomeomorph a r hr)

theorem cutoffRescale_tsupport_image (η : E → ℝ) (a : E) {r : ℝ} (hr : r ≠ 0) :
    tsupport (cutoffRescale η a r) = (fun x => a+r • x) '' tsupport η := by
  rw [cutoffRescale_tsupport_preimage η a hr]
  ext x
  constructor
  · intro hx
    exact ⟨cutoffRescaleMap a r x,hx,cutoffRescaleMap_inverse_left a hr x⟩
  · rintro ⟨y,hy,rfl⟩
    change cutoffRescaleMap a r (a+r • y) ∈ tsupport η
    rwa [cutoffRescaleMap_inverse_right a hr]

theorem cutoffRescale_hasCompactSupport {η : E → ℝ} (hcη : HasCompactSupport η)
    (a : E) {r : ℝ} (hr : r ≠ 0) : HasCompactSupport (cutoffRescale η a r) :=
  hcη.comp_homeomorph (cutoffRescaleHomeomorph a r hr)

theorem cutoffRescale_plateau_image {η : E → ℝ} {K : Set E}
    (hη : ∀ x ∈ K, η x = 1) (a : E) {r : ℝ} (hr : r ≠ 0) :
    ∀ x ∈ (fun y => a+r • y) '' K, cutoffRescale η a r x = 1 := by
  rintro x ⟨y,hy,rfl⟩
  change η (cutoffRescaleMap a r (a+r • y)) = 1
  rw [cutoffRescaleMap_inverse_right a hr]
  exact hη y hy

theorem cutoffRescale_tsupport_closedBall {η : E → ℝ} {R : ℝ}
    (hη : tsupport η ⊆ Metric.closedBall (0 : E) R) (a : E) {r : ℝ} (hr : 0 < r) :
    tsupport (cutoffRescale η a r) ⊆ Metric.closedBall a (r*R) := by
  rw [cutoffRescale_tsupport_image η a hr.ne']
  rintro x ⟨y,hy,rfl⟩
  have hyn : ‖y‖ ≤ R := by simpa only [Metric.mem_closedBall,dist_zero_right] using hη hy
  rw [Metric.mem_closedBall,dist_eq_norm]
  simpa only [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hr] using
    mul_le_mul_of_nonneg_left hyn hr.le

end TheoremT.Continuum
