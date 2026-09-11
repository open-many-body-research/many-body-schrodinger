import LinearRadiusWeakLaplacian_v1
import PairDistanceLinearMaps_v1
import PhysicalDistanceLocalIntegrability_v1

/-! Physical nuclear and pair distance Laplacians on full configuration space.
Every singular-integrability and collision-nullity premise is discharged. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace TheoremT.Continuum

theorem nuclear_linearRadiusHessian_trace {N : ℕ} (i : Fin N) (x : Configuration N) :
    (∑ k : Coordinate N, linearRadiusHessian (electronPositionCLM i)
      (coordinateVector k) (coordinateVector k) x) = 2/‖position x i‖ := by
  rw [linearRadiusHessian_trace,electronPositionCLM_column_norm_sq_sum,
    electronPositionCLM_column_inner_sq_sum,electronPositionCLM_apply]
  by_cases h : position x i=0
  · simp [h]
  · have hn := norm_ne_zero_iff.mpr h
    field_simp
    <;> ring

theorem pair_linearRadiusHessian_trace {N : ℕ} (i j : Fin N) (hij : i ≠ j) (x : Configuration N) :
    (∑ k : Coordinate N, linearRadiusHessian (pairDifferenceCLM i j)
      (coordinateVector k) (coordinateVector k) x) = 4/‖position x i-position x j‖ := by
  rw [linearRadiusHessian_trace,pairDifferenceCLM_column_norm_sq_sum i j hij,
    pairDifferenceCLM_column_inner_sq_sum i j hij,pairDifferenceCLM_apply]
  by_cases h : position x i-position x j=0
  · simp [h]
  · have hn := norm_ne_zero_iff.mpr h
    field_simp
    <;> ring

theorem nuclear_radius_weak_laplacian_test {N : ℕ} (i : Fin N)
    {φ : Configuration N → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∫ x, φ x*(2/‖position x i‖)) =
      ∫ x, (∑ k : Coordinate N, fderiv ℝ
        (fun y => fderiv ℝ φ y (coordinateVector k)) x (coordinateVector k))*‖position x i‖ := by
  have hne : ∀ᵐ x, electronPositionCLM i x ≠ 0 := by
    filter_upwards [ae_collisionFree N] with x hx
    exact hx.1 i
  simpa only [nuclear_linearRadiusHessian_trace,electronPositionCLM_apply] using
    linear_radius_weak_laplacian_test (electronPositionCLM i) (nuclear_inverse_locallyIntegrable i)
      hne hφ hc

theorem pair_radius_weak_laplacian_test {N : ℕ} (i j : Fin N) (hij : i ≠ j)
    {φ : Configuration N → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∫ x, φ x*(4/‖position x i-position x j‖)) =
      ∫ x, (∑ k : Coordinate N, fderiv ℝ
        (fun y => fderiv ℝ φ y (coordinateVector k)) x (coordinateVector k))*
          ‖position x i-position x j‖ := by
  have hne : ∀ᵐ x, pairDifferenceCLM i j x ≠ 0 := by
    filter_upwards [ae_collisionFree N] with x hx
    exact sub_ne_zero.mpr (hx.2 i j hij)
  simpa only [pair_linearRadiusHessian_trace i j hij,pairDifferenceCLM_apply] using
    linear_radius_weak_laplacian_test (pairDifferenceCLM i j) (pair_inverse_locallyIntegrable i j hij)
      hne hφ hc

#print axioms nuclear_radius_weak_laplacian_test
#print axioms pair_radius_weak_laplacian_test
end TheoremT.Continuum
