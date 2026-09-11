import SmoothConfigurationRadius_v1
import Mathlib.Analysis.Calculus.Deriv.Inv

/-! Actual mixed second derivatives of the smooth physical radius. The
coarse bound2 is dimension independent and valid also on collision strata. -/
noncomputable section
open scoped ContDiff
namespace TheoremT.Continuum

theorem smoothConfigurationRadius_ge_one {N : ℕ} (x : Configuration N) :
    1 ≤ smoothConfigurationRadius N x := by
  nlinarith [smoothConfigurationRadius_sq x,smoothConfigurationRadius_pos x,sq_nonneg ‖x‖]

theorem smoothConfigurationRadius_mixed_partial {N : ℕ}
    (x : Configuration N) (k l : Coordinate N) :
    fderiv ℝ (fun y => fderiv ℝ (smoothConfigurationRadius N) y (coordinateVector k))
      x (coordinateVector l) =
      (coordinateVector l k)/smoothConfigurationRadius N x -
        ((x k/smoothConfigurationRadius N x)*(x l/smoothConfigurationRadius N x)) /
          smoothConfigurationRadius N x := by
  have he : (fun y => fderiv ℝ (smoothConfigurationRadius N) y (coordinateVector k)) =
      (fun y => y k * (smoothConfigurationRadius N y)⁻¹) := by
    funext y
    rw [smoothConfigurationRadius_partial,div_eq_mul_inv]
  rw [he]
  have hr := ((smoothConfigurationRadius_contDiff N).differentiable (by simp) x).hasFDerivAt
  have hc := (EuclideanSpace.proj (𝕜 := ℝ) k).hasFDerivAt (x := x)
  have h := hc.mul ((hasFDerivAt_inv (smoothConfigurationRadius_pos x).ne').comp x hr)
  change HasFDerivAt (fun y => y k*(smoothConfigurationRadius N y)⁻¹) _ x at h
  rw [h.fderiv]
  simp [smoothConfigurationRadius_partial,EuclideanSpace.coe_proj]
  field_simp
  <;> ring

theorem smoothConfigurationRadius_mixed_partial_abs_le_two {N : ℕ}
    (x : Configuration N) (k l : Coordinate N) :
    |fderiv ℝ (fun y => fderiv ℝ (smoothConfigurationRadius N) y (coordinateVector k))
      x (coordinateVector l)| ≤ 2 := by
  rw [smoothConfigurationRadius_mixed_partial]
  have hδ : |coordinateVector l k| ≤ 1 := by
    by_cases h : l = k
    · subst l; simp [coordinateVector]
    · simp [coordinateVector,h,Ne.symm h]
  have hk : |x k/smoothConfigurationRadius N x| ≤ 1 := by
    simpa only [smoothConfigurationRadius_partial] using
      smoothConfigurationRadius_partial_abs_le_one x k
  have hl : |x l/smoothConfigurationRadius N x| ≤ 1 := by
    simpa only [smoothConfigurationRadius_partial] using
      smoothConfigurationRadius_partial_abs_le_one x l
  have hr := smoothConfigurationRadius_ge_one x
  have hp := smoothConfigurationRadius_pos x
  have hfirst : |coordinateVector l k/smoothConfigurationRadius N x| ≤ 1 := by
    rw [abs_div,abs_of_pos hp]
    exact (div_le_one hp).mpr (hδ.trans hr)
  have hsecond : |((x k/smoothConfigurationRadius N x)*
      (x l/smoothConfigurationRadius N x))/smoothConfigurationRadius N x| ≤ 1 := by
    rw [abs_div,abs_mul,abs_of_pos hp]
    apply (div_le_one hp).mpr
    exact (mul_le_mul hk hl (abs_nonneg _) (by norm_num)).trans (by simpa using hr)
  exact (abs_sub _ _).trans (by linarith)

#print axioms smoothConfigurationRadius_mixed_partial
#print axioms smoothConfigurationRadius_mixed_partial_abs_le_two
end TheoremT.Continuum
