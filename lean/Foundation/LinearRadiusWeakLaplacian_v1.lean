import LinearRadiusWeakHessian_v1

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace TheoremT.Continuum

theorem linear_radius_weak_laplacian_test {N : ℕ}
    (A : Configuration N →L[ℝ] Position)
    (hb : LocallyIntegrable (fun x => ‖A x‖⁻¹) volume)
    (hne : ∀ᵐ x, A x ≠ 0)
    {φ : Configuration N → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∫ x, φ x*(∑ k : Coordinate N, linearRadiusHessian A (coordinateVector k) (coordinateVector k) x)) =
      ∫ x, (∑ k : Coordinate N, fderiv ℝ
        (fun y => fderiv ℝ φ y (coordinateVector k)) x (coordinateVector k))*‖A x‖ := by
  have hi (k : Coordinate N) : Integrable (fun x => φ x*linearRadiusHessian A
      (coordinateVector k) (coordinateVector k) x) := by
    simpa only [smul_eq_mul] using (linearRadiusHessian_locallyIntegrable A hb hne
      (coordinateVector k) (coordinateVector k)).integrable_smul_left_of_hasCompactSupport hφ.continuous hc
  have hi' (k : Coordinate N) : Integrable (fun x => fderiv ℝ
      (fun y => fderiv ℝ φ y (coordinateVector k)) x (coordinateVector k)*‖A x‖) := by
    have hd : ContDiff ℝ ∞ (fun y => fderiv ℝ φ y (coordinateVector k)) :=
      (hφ.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
    exact (((hd.continuous_fderiv (by simp)).clm_apply continuous_const).mul A.continuous.norm).integrable_of_hasCompactSupport
      ((hc.fderiv_apply ℝ (coordinateVector k)).fderiv_apply ℝ (coordinateVector k)).mul_right
  calc
    _ = ∫ x, ∑ k : Coordinate N, φ x*linearRadiusHessian A (coordinateVector k) (coordinateVector k) x := by
      simp_rw [Finset.mul_sum]
    _ = ∑ k : Coordinate N, ∫ x, φ x*linearRadiusHessian A (coordinateVector k) (coordinateVector k) x :=
      integral_finsetSum _ (fun k _ => hi k)
    _ = ∑ k : Coordinate N, ∫ x, fderiv ℝ
        (fun y => fderiv ℝ φ y (coordinateVector k)) x (coordinateVector k)*‖A x‖ := by
      apply Finset.sum_congr rfl
      intro k _
      exact linear_radius_weak_hessian_test A hb hne hφ hc (coordinateVector k) (coordinateVector k)
    _ = ∫ x, ∑ k : Coordinate N, fderiv ℝ
        (fun y => fderiv ℝ φ y (coordinateVector k)) x (coordinateVector k)*‖A x‖ :=
      (integral_finsetSum _ (fun k _ => hi' k)).symm
    _ = _ := by simp_rw [Finset.sum_mul]

theorem linearRadiusHessian_trace {N : ℕ} (A : Configuration N →L[ℝ] Position)
    (x : Configuration N) :
    (∑ k : Coordinate N, linearRadiusHessian A (coordinateVector k) (coordinateVector k) x) =
      (∑ k : Coordinate N, ‖A (coordinateVector k)‖^2)/‖A x‖-
        (∑ k : Coordinate N, (inner ℝ (A x) (A (coordinateVector k)))^2)/‖A x‖^3 := by
  unfold linearRadiusHessian
  simp_rw [real_inner_self_eq_norm_sq,← pow_two]
  rw [Finset.sum_sub_distrib,← Finset.sum_div,← Finset.sum_div]

#print axioms linear_radius_weak_laplacian_test
end TheoremT.Continuum
