import ConfigurationRadiusWeakHessian_v1

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace TheoremT.Continuum

theorem configuration_radius_weak_gradient_test {N : ℕ} (hN : 0 < N)
    {φ : Configuration N → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (k : Coordinate N) :
    (∫ x, φ x*(x k/‖x‖)) = -(∫ x, fderiv ℝ φ x (coordinateVector k)*‖x‖) := by
  have hb : LocallyIntegrable (fun _ : Configuration N => (1:ℝ)) volume :=
    continuous_const.locallyIntegrable
  have hl := compact_real_test_integral_tendsto_locally_dominated hb
    (fun n => ((regularizedConfigurationRadius_contDiff N (radiusRegularization_pos n)).continuous_fderiv
      (by simp)).clm_apply continuous_const |>.aestronglyMeasurable)
    (fun n => Eventually.of_forall (fun x => by
      simpa only [Real.norm_eq_abs,abs_one] using
        regularizedConfigurationRadius_partial_abs_le_one (radiusRegularization_pos n) x k))
    (by
      filter_upwards [configuration_ae_ne_zero hN] with x hx
      exact regularizedConfigurationRadius_partial_tendsto radiusRegularization_pos
        radiusRegularization_tendsto hx k)
    hφ.continuous hc
  have htest : Continuous (fun x => fderiv ℝ φ x (coordinateVector k)) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hbF : LocallyIntegrable (fun x : Configuration N => ‖x‖+1) volume :=
    (continuous_norm.add continuous_const).locallyIntegrable
  have hr := compact_real_test_integral_tendsto_locally_dominated hbF
    (fun n => (regularizedConfigurationRadius_contDiff N (radiusRegularization_pos n)).continuous.aestronglyMeasurable)
    (fun n => Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs,Real.norm_eq_abs,
        abs_of_pos (regularizedConfigurationRadius_pos (radiusRegularization_pos n) x),
        abs_of_nonneg (by positivity : 0 ≤ ‖x‖+1)]
      exact regularizedConfigurationRadius_le_norm_add_one (radiusRegularization_pos n)
        (radiusRegularization_le_one n) x))
    (Eventually.of_forall (fun x => regularizedConfigurationRadius_tendsto radiusRegularization_tendsto x))
    htest (hc.fderiv_apply ℝ (coordinateVector k))
  have he (n : ℕ) := configuration_integral_mul_fderiv_compact (hφ.of_le (by simp))
    ((regularizedConfigurationRadius_contDiff N (radiusRegularization_pos n)).of_le (by simp)) hc
    (coordinateVector k)
  exact tendsto_nhds_unique hl (hr.neg.congr' (Eventually.of_forall (fun n => (he n).symm)))

#print axioms configuration_radius_weak_gradient_test
end TheoremT.Continuum
