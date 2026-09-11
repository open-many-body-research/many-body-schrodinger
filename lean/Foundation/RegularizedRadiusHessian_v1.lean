import RegularizedConfigurationRadius_v1

/-! Uniform singular domination for the actual Hessian of the regularized
radius. Bounds through the zero-regularization limit are stated off the origin. -/
noncomputable section
open scoped ContDiff
namespace TheoremT.Continuum

theorem regularizedConfigurationRadius_mixed_partial {N : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (x : Configuration N) (k l : Coordinate N) :
    fderiv ℝ (fun y => fderiv ℝ (regularizedConfigurationRadius N δ) y (coordinateVector k))
      x (coordinateVector l) =
      (coordinateVector l k)/regularizedConfigurationRadius N δ x -
        ((x k/regularizedConfigurationRadius N δ x)*(x l/regularizedConfigurationRadius N δ x)) /
          regularizedConfigurationRadius N δ x := by
  have he : (fun y => fderiv ℝ (regularizedConfigurationRadius N δ) y (coordinateVector k)) =
      (fun y => y k*(regularizedConfigurationRadius N δ y)⁻¹) := by
    funext y; rw [regularizedConfigurationRadius_partial hδ,div_eq_mul_inv]
  rw [he]
  have hr := ((regularizedConfigurationRadius_contDiff N hδ).differentiable (by simp) x).hasFDerivAt
  have hc := (EuclideanSpace.proj (𝕜 := ℝ) k).hasFDerivAt (x := x)
  have h := hc.mul ((hasFDerivAt_inv (regularizedConfigurationRadius_pos hδ x).ne').comp x hr)
  change HasFDerivAt (fun y => y k*(regularizedConfigurationRadius N δ y)⁻¹) _ x at h
  rw [h.fderiv]
  simp [regularizedConfigurationRadius_partial hδ,EuclideanSpace.coe_proj]
  field_simp
  <;> ring

theorem regularizedConfigurationRadius_mixed_abs_bound {N : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (x : Configuration N) (k l : Coordinate N) :
    |fderiv ℝ (fun y => fderiv ℝ (regularizedConfigurationRadius N δ) y (coordinateVector k))
      x (coordinateVector l)| ≤ 2/regularizedConfigurationRadius N δ x := by
  rw [regularizedConfigurationRadius_mixed_partial hδ]
  have hδkl : |coordinateVector l k| ≤ 1 := by
    by_cases h : l=k
    · subst l; simp [coordinateVector]
    · simp [coordinateVector,h,Ne.symm h]
  have hk : |x k/regularizedConfigurationRadius N δ x| ≤ 1 := by
    simpa only [regularizedConfigurationRadius_partial hδ] using
      regularizedConfigurationRadius_partial_abs_le_one hδ x k
  have hl : |x l/regularizedConfigurationRadius N δ x| ≤ 1 := by
    simpa only [regularizedConfigurationRadius_partial hδ] using
      regularizedConfigurationRadius_partial_abs_le_one hδ x l
  have hp := regularizedConfigurationRadius_pos hδ x
  have hprod : |(x k/regularizedConfigurationRadius N δ x)*
      (x l/regularizedConfigurationRadius N δ x)| ≤ 1 := by
    rw [abs_mul]
    simpa using mul_le_mul hk hl (abs_nonneg _) (by norm_num)
  calc
    _ ≤ |coordinateVector l k/regularizedConfigurationRadius N δ x|+
        |((x k/regularizedConfigurationRadius N δ x)*(x l/regularizedConfigurationRadius N δ x))/
          regularizedConfigurationRadius N δ x| := abs_sub _ _
    _ ≤ 1/regularizedConfigurationRadius N δ x+1/regularizedConfigurationRadius N δ x := by
      simp only [abs_div,abs_of_pos hp]
      exact add_le_add (div_le_div_of_nonneg_right hδkl hp.le)
        (div_le_div_of_nonneg_right hprod hp.le)
    _ = _ := by ring

theorem regularizedConfigurationRadius_mixed_coulomb_bound {N : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {x : Configuration N} (hx : x ≠ 0) (k l : Coordinate N) :
    |fderiv ℝ (fun y => fderiv ℝ (regularizedConfigurationRadius N δ) y (coordinateVector k))
      x (coordinateVector l)| ≤ 2/‖x‖ :=
  (regularizedConfigurationRadius_mixed_abs_bound hδ x k l).trans
    (div_le_div_of_nonneg_left (by norm_num) (norm_pos_iff.mpr hx)
      (norm_le_regularizedConfigurationRadius hδ x))

#print axioms regularizedConfigurationRadius_mixed_coulomb_bound
end TheoremT.Continuum
