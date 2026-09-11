import RegularizedLinearRadius_v1

noncomputable section
open scoped ContDiff
namespace TheoremT.Continuum

theorem norm_le_regularizedLinearRadius {N : ℕ} (A : Configuration N →L[ℝ] Position)
    {δ : ℝ} (hδ : 0 < δ) (x : Configuration N) : ‖A x‖ ≤ regularizedLinearRadius A δ x := by
  nlinarith [regularizedLinearRadius_sq A hδ x,regularizedLinearRadius_pos A hδ x,norm_nonneg (A x)]

theorem regularizedLinearRadius_le_norm_add_one {N : ℕ} (A : Configuration N →L[ℝ] Position)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (x : Configuration N) :
    regularizedLinearRadius A δ x ≤ ‖A x‖+1 := by
  nlinarith [regularizedLinearRadius_sq A hδ x,regularizedLinearRadius_pos A hδ x,norm_nonneg (A x)]

theorem regularizedLinearRadius_partial_abs_bound {N : ℕ} (A : Configuration N →L[ℝ] Position)
    {δ : ℝ} (hδ : 0 < δ) (x v : Configuration N) :
    |fderiv ℝ (regularizedLinearRadius A δ) x v| ≤ ‖A v‖ := by
  rw [regularizedLinearRadius_fderiv_apply A hδ,abs_div,
    abs_of_pos (regularizedLinearRadius_pos A hδ x)]
  apply (div_le_iff₀ (regularizedLinearRadius_pos A hδ x)).mpr
  calc
    _ ≤ ‖A x‖*‖A v‖ := abs_real_inner_le_norm _ _
    _ ≤ regularizedLinearRadius A δ x*‖A v‖ :=
      mul_le_mul_of_nonneg_right (norm_le_regularizedLinearRadius A hδ x) (norm_nonneg _)
    _ = _ := mul_comm _ _

theorem regularizedLinearRadius_mixed_abs_bound {N : ℕ} (A : Configuration N →L[ℝ] Position)
    {δ : ℝ} (hδ : 0 < δ) (x v w : Configuration N) :
    |fderiv ℝ (fun y => fderiv ℝ (regularizedLinearRadius A δ) y v) x w| ≤
      2*‖A v‖*‖A w‖/regularizedLinearRadius A δ x := by
  have hv : |inner ℝ (A x) (A v)/regularizedLinearRadius A δ x| ≤ ‖A v‖ := by
    simpa only [regularizedLinearRadius_fderiv_apply A hδ] using
      regularizedLinearRadius_partial_abs_bound A hδ x v
  have hw : |inner ℝ (A x) (A w)/regularizedLinearRadius A δ x| ≤ ‖A w‖ := by
    simpa only [regularizedLinearRadius_fderiv_apply A hδ] using
      regularizedLinearRadius_partial_abs_bound A hδ x w
  have hp := regularizedLinearRadius_pos A hδ x
  have hprod := mul_le_mul hv hw (abs_nonneg _) (norm_nonneg _)
  simp only [abs_div,abs_of_pos hp] at hprod
  rw [regularizedLinearRadius_mixed_partial A hδ]
  have he : inner ℝ (A x) (A v)*inner ℝ (A x) (A w)/(regularizedLinearRadius A δ x)^3 =
      ((inner ℝ (A x) (A v)/regularizedLinearRadius A δ x)*
        (inner ℝ (A x) (A w)/regularizedLinearRadius A δ x))/regularizedLinearRadius A δ x := by ring
  rw [he]
  calc
    _ ≤ |inner ℝ (A w) (A v)/regularizedLinearRadius A δ x|+
      |((inner ℝ (A x) (A v)/regularizedLinearRadius A δ x)*
        (inner ℝ (A x) (A w)/regularizedLinearRadius A δ x))/regularizedLinearRadius A δ x| := abs_sub _ _
    _ ≤ (‖A w‖*‖A v‖)/regularizedLinearRadius A δ x+
        (‖A v‖*‖A w‖)/regularizedLinearRadius A δ x := by
      simp only [abs_div,abs_of_pos hp,abs_mul]
      exact add_le_add (div_le_div_of_nonneg_right (abs_real_inner_le_norm _ _) hp.le)
        (div_le_div_of_nonneg_right hprod hp.le)
    _ = _ := by ring

theorem regularizedLinearRadius_mixed_coulomb_bound {N : ℕ}
    (A : Configuration N →L[ℝ] Position) {δ : ℝ} (hδ : 0 < δ)
    {x : Configuration N} (hx : A x ≠ 0) (v w : Configuration N) :
    |fderiv ℝ (fun y => fderiv ℝ (regularizedLinearRadius A δ) y v) x w| ≤
      2*‖A v‖*‖A w‖/‖A x‖ :=
  (regularizedLinearRadius_mixed_abs_bound A hδ x v w).trans
    (div_le_div_of_nonneg_left (by positivity) (norm_pos_iff.mpr hx)
      (norm_le_regularizedLinearRadius A hδ x))

#print axioms regularizedLinearRadius_mixed_coulomb_bound
end TheoremT.Continuum
