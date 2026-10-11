import SmoothCutoffRescaleGeometry_v1
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
Exact derivatives and quantitative derivative bounds for a translated,
rescaled smooth cutoff. Every norm is the given norm on the source space;
no Euclidean/product norm identification is made. The exact chain rules
hold for every real scale (using the field inverse); decay bounds use a
strictly positive scale. The second derivative is ordered explicitly.
-/
noncomputable section
open scoped ContDiff

namespace TheoremT.Continuum

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem cutoffRescale_first {η : E → ℝ} (hη : ContDiff ℝ ∞ η)
    (a : E) (r : ℝ) (x v : E) :
    fderiv ℝ (cutoffRescale η a r) x v =
      r⁻¹ * fderiv ℝ η (cutoffRescaleMap a r x) v := by
  have hm := ((hasFDerivAt_id (𝕜 := ℝ) x).sub_const a).const_smul r⁻¹
  have hb := (hη.differentiable (by simp) (cutoffRescaleMap a r x)).hasFDerivAt
  have hh := hb.comp x hm
  change HasFDerivAt (𝕜 := ℝ) (fun y => η (r⁻¹ • (y - a))) _ x at hh
  change fderiv ℝ (fun y => η (r⁻¹ • (y - a))) x v = _
  rw [hh.fderiv]
  simp [cutoffRescaleMap]

theorem cutoffRescale_second {η : E → ℝ} (hη : ContDiff ℝ ∞ η)
    (a : E) (r : ℝ) (x v w : E) :
    fderiv ℝ (fun y => fderiv ℝ (cutoffRescale η a r) y v) x w =
      (r⁻¹) ^ 2 * fderiv ℝ (fun y => fderiv ℝ η y v) (cutoffRescaleMap a r x) w := by
  have he : (fun y => fderiv ℝ (cutoffRescale η a r) y v) =
      fun y => r⁻¹ • fderiv ℝ η (cutoffRescaleMap a r y) v := by
    funext y
    exact cutoffRescale_first hη a r y v
  rw [he]
  have hd : ContDiff ℝ ∞ (fun y => fderiv ℝ η y v) :=
    (hη.fderiv_right (by simp : (∞ : WithTop ℕ∞) + 1 ≤ ∞)).clm_apply contDiff_const
  have hm := ((hasFDerivAt_id (𝕜 := ℝ) x).sub_const a).const_smul r⁻¹
  have hb := (hd.differentiable (by simp) (cutoffRescaleMap a r x)).hasFDerivAt
  have hh := (hb.comp x hm).const_smul r⁻¹
  change HasFDerivAt (𝕜 := ℝ)
    (fun y => r⁻¹ • fderiv ℝ η (cutoffRescaleMap a r y) v) _ x at hh
  rw [hh.fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
  ring

theorem smooth_directional_second_eq_fderiv_fderiv
    {η : E → ℝ} (hη : ContDiff ℝ ∞ η) (x v w : E) :
    fderiv ℝ (fun y => fderiv ℝ η y v) x w =
      (fderiv ℝ (fderiv ℝ η) x w) v := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ η) :=
    hη.fderiv_right (by simp : (∞ : WithTop ℕ∞) + 1 ≤ ∞)
  rw [fderiv_clm_apply (hd.differentiable (by simp) x) (differentiableAt_const v)]
  simp

theorem cutoffRescale_first_bound {η : E → ℝ} (hη : ContDiff ℝ ∞ η)
    {L1 : ℝ} (hL1 : ∀ y : E, ‖fderiv ℝ η y‖ ≤ L1)
    (a : E) {r : ℝ} (hr : 0 < r) (x v : E) :
    |fderiv ℝ (cutoffRescale η a r) x v| ≤ (L1 / r) * ‖v‖ := by
  rw [cutoffRescale_first hη, abs_mul, abs_inv, abs_of_pos hr]
  have hb : |fderiv ℝ η (cutoffRescaleMap a r x) v| ≤ L1 * ‖v‖ := by
    rw [← Real.norm_eq_abs]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hL1 _) (norm_nonneg _))
  simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
    mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hr.le)

theorem cutoffRescale_second_bound {η : E → ℝ} (hη : ContDiff ℝ ∞ η)
    {L2 : ℝ} (hL2 : ∀ y : E, ‖fderiv ℝ (fderiv ℝ η) y‖ ≤ L2)
    (a : E) {r : ℝ} (hr : 0 < r) (x v w : E) :
    |fderiv ℝ (fun y => fderiv ℝ (cutoffRescale η a r) y v) x w| ≤
      (L2 / r ^ 2) * ‖v‖ * ‖w‖ := by
  rw [cutoffRescale_second hη, abs_mul, abs_pow, abs_inv, abs_of_pos hr]
  have hb : |fderiv ℝ (fun y => fderiv ℝ η y v) (cutoffRescaleMap a r x) w| ≤
      L2 * ‖v‖ * ‖w‖ := by
    rw [smooth_directional_second_eq_fderiv_fderiv hη, ← Real.norm_eq_abs]
    calc
      _ ≤ ‖fderiv ℝ (fderiv ℝ η) (cutoffRescaleMap a r x) w‖ * ‖v‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖fderiv ℝ (fderiv ℝ η) (cutoffRescaleMap a r x)‖ * ‖w‖) * ‖v‖ :=
        mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ ≤ (L2 * ‖w‖) * ‖v‖ := by
        gcongr
        exact hL2 _
      _ = _ := by ring
  simpa only [div_eq_mul_inv, inv_pow, mul_assoc, mul_comm, mul_left_comm] using
    mul_le_mul_of_nonneg_left hb (sq_nonneg r⁻¹)

#print axioms cutoffRescale_first
#print axioms cutoffRescale_second
#print axioms smooth_directional_second_eq_fderiv_fderiv
#print axioms cutoffRescale_first_bound
#print axioms cutoffRescale_second_bound

end TheoremT.Continuum
