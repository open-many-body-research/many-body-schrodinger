import ConfigurationLocalDominated_v1
import RegularizedRadiusLimitBounds_v1

/-! The actual distributional Hessian of |x| on R^(3N), N>=1.
The origin is included in the test identity; its nullity alone is not used
as a substitute for proving the absence of a singular distribution there. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff Topology
namespace TheoremT.Continuum

theorem configuration_radius_weak_hessian_test {N : ℕ} (hN : 0 < N)
    {φ : Configuration N → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (k l : Coordinate N) :
    (∫ x, φ x*((coordinateVector l k)/‖x‖-x k*x l/‖x‖^3)) =
      ∫ x, fderiv ℝ (fun y => fderiv ℝ φ y (coordinateVector l)) x (coordinateVector k)*‖x‖ := by
  have hb : LocallyIntegrable (fun x : Configuration N => 2*‖x‖⁻¹) volume := by
    rw [locallyIntegrable_iff]
    intro K hK
    exact ((configuration_inverse_radius_locallyIntegrable hN).integrableOn_isCompact hK).const_mul 2
  have hd (n : ℕ) : ContDiff ℝ ∞
      (fun y => fderiv ℝ (regularizedConfigurationRadius N (radiusRegularization n)) y
        (coordinateVector k)) :=
    ((regularizedConfigurationRadius_contDiff N (radiusRegularization_pos n)).fderiv_right
      (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  have hl := compact_real_test_integral_tendsto_locally_dominated hb
    (fun n => ((hd n).continuous_fderiv (by simp)).clm_apply continuous_const |>.aestronglyMeasurable)
    (fun n => by
      filter_upwards [configuration_ae_ne_zero hN] with x hx
      rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ 2*‖x‖⁻¹)]
      simpa only [div_eq_mul_inv] using
        regularizedConfigurationRadius_mixed_coulomb_bound (radiusRegularization_pos n) hx k l)
    (by
      filter_upwards [configuration_ae_ne_zero hN] with x hx
      exact regularizedConfigurationRadius_hessian_tendsto radiusRegularization_pos
        radiusRegularization_tendsto hx k l)
    hφ.continuous hc
  have hdφ : ContDiff ℝ ∞ (fun y => fderiv ℝ φ y (coordinateVector l)) :=
    (hφ.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  have htest : Continuous (fun x => fderiv ℝ
      (fun y => fderiv ℝ φ y (coordinateVector l)) x (coordinateVector k)) :=
    (hdφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have htestc := (hc.fderiv_apply ℝ (coordinateVector l)).fderiv_apply ℝ (coordinateVector k)
  have hbF : LocallyIntegrable (fun x : Configuration N => ‖x‖+1) volume :=
    (continuous_norm.add continuous_const).locallyIntegrable
  have hr := compact_real_test_integral_tendsto_locally_dominated hbF
    (fun n => (regularizedConfigurationRadius_contDiff N (radiusRegularization_pos n)).continuous.aestronglyMeasurable)
    (fun n => by
      filter_upwards with x
      rw [Real.norm_eq_abs,Real.norm_eq_abs,
        abs_of_pos (regularizedConfigurationRadius_pos (radiusRegularization_pos n) x),
        abs_of_nonneg (by positivity : 0 ≤ ‖x‖+1)]
      exact regularizedConfigurationRadius_le_norm_add_one (radiusRegularization_pos n)
        (radiusRegularization_le_one n) x)
    (Eventually.of_forall (fun x => regularizedConfigurationRadius_tendsto radiusRegularization_tendsto x))
    htest htestc
  have he (n : ℕ) := configuration_integral_mixed_transfer hφ
    (regularizedConfigurationRadius_contDiff N (radiusRegularization_pos n)) hc
    (coordinateVector k) (coordinateVector l)
  exact tendsto_nhds_unique hl (hr.congr' (Eventually.of_forall (fun n => (he n).symm)))

#print axioms configuration_radius_weak_hessian_test
end TheoremT.Continuum
