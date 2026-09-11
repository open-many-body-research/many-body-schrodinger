import LinearRadiusWeakHessian_v1

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace TheoremT.Continuum

def linearRadiusGradient {N : ℕ} (A : Configuration N →L[ℝ] Position)
    (v x : Configuration N) : ℝ := inner ℝ (A x) (A v)/‖A x‖

theorem linearRadiusGradient_abs_bound {N : ℕ} (A : Configuration N →L[ℝ] Position)
    (v x : Configuration N) : |linearRadiusGradient A v x| ≤ ‖A v‖ := by
  by_cases hx : A x=0
  · simp [linearRadiusGradient,hx]
  · apply le_of_tendsto ((regularizedLinearRadius_partial_tendsto A radiusRegularization_pos
      radiusRegularization_tendsto hx v).abs)
    exact Eventually.of_forall (fun n => regularizedLinearRadius_partial_abs_bound A
      (radiusRegularization_pos n) x v)

theorem linear_radius_weak_gradient_test {N : ℕ} (A : Configuration N →L[ℝ] Position)
    (hne : ∀ᵐ x, A x ≠ 0)
    {φ : Configuration N → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (v : Configuration N) :
    (∫ x, φ x*linearRadiusGradient A v x) = -(∫ x, fderiv ℝ φ x v*‖A x‖) := by
  have hb : LocallyIntegrable (fun _ : Configuration N => ‖A v‖) volume :=
    continuous_const.locallyIntegrable
  have hl := compact_real_test_integral_tendsto_locally_dominated hb
    (fun n => ((regularizedLinearRadius_contDiff A (radiusRegularization_pos n)).continuous_fderiv
      (by simp)).clm_apply (continuous_const : Continuous (fun _ : Configuration N => v)) |>.aestronglyMeasurable)
    (fun n => Eventually.of_forall (fun x => by
      simpa only [Real.norm_eq_abs,abs_norm] using
        regularizedLinearRadius_partial_abs_bound A (radiusRegularization_pos n) x v))
    (by
      filter_upwards [hne] with x hx
      exact regularizedLinearRadius_partial_tendsto A radiusRegularization_pos
        radiusRegularization_tendsto hx v)
    hφ.continuous hc
  have htest : Continuous (fun x => fderiv ℝ φ x v) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hbF : LocallyIntegrable (fun x : Configuration N => ‖A x‖+1) volume :=
    (A.continuous.norm.add continuous_const).locallyIntegrable
  have hr := compact_real_test_integral_tendsto_locally_dominated hbF
    (fun n => (regularizedLinearRadius_contDiff A (radiusRegularization_pos n)).continuous.aestronglyMeasurable)
    (fun n => Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs,Real.norm_eq_abs,
        abs_of_pos (regularizedLinearRadius_pos A (radiusRegularization_pos n) x),
        abs_of_nonneg (by positivity : 0 ≤ ‖A x‖+1)]
      exact regularizedLinearRadius_le_norm_add_one A (radiusRegularization_pos n)
        (radiusRegularization_le_one n) x))
    (Eventually.of_forall (fun x => regularizedLinearRadius_tendsto A radiusRegularization_tendsto x))
    htest (hc.fderiv_apply ℝ v)
  have he (n : ℕ) := configuration_integral_mul_fderiv_compact (hφ.of_le (by simp))
    ((regularizedLinearRadius_contDiff A (radiusRegularization_pos n)).of_le (by simp)) hc v
  exact tendsto_nhds_unique hl (hr.neg.congr' (Eventually.of_forall (fun n => (he n).symm)))

#print axioms linear_radius_weak_gradient_test
end TheoremT.Continuum
