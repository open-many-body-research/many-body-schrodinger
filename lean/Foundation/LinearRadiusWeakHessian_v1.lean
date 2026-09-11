import LinearRadiusLimits_v1
import ConfigurationLocalDominated_v1

/-! A conditional transfer lemma for linear distances. The inverse-distance
integrability and collision-nullity premises are discharged for the physical
nuclear and pair maps in subsequent modules. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff Topology
namespace TheoremT.Continuum

theorem linearRadiusHessian_locallyIntegrable {N : ℕ}
    (A : Configuration N →L[ℝ] Position)
    (hb : LocallyIntegrable (fun x => ‖A x‖⁻¹) volume)
    (hne : ∀ᵐ x, A x ≠ 0) (v w : Configuration N) :
    LocallyIntegrable (linearRadiusHessian A v w) volume := by
  have hbc : LocallyIntegrable (fun x => (2*‖A v‖*‖A w‖)*‖A x‖⁻¹) volume := by
    simpa only [Pi.smul_def,smul_eq_mul] using hb.smul (2*‖A v‖*‖A w‖)
  apply hbc.mono
  · have hm : Measurable (linearRadiusHessian A v w) := by
      unfold linearRadiusHessian
      fun_prop
    exact hm.aestronglyMeasurable
  · filter_upwards [hne] with x hx
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity : 0 ≤ 2*‖A v‖*‖A w‖*‖A x‖⁻¹)]
    simpa only [Real.norm_eq_abs,div_eq_mul_inv] using linearRadiusHessian_bound A hx v w

theorem linear_radius_weak_hessian_test {N : ℕ}
    (A : Configuration N →L[ℝ] Position)
    (hb : LocallyIntegrable (fun x => ‖A x‖⁻¹) volume)
    (hne : ∀ᵐ x, A x ≠ 0)
    {φ : Configuration N → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (v w : Configuration N) :
    (∫ x, φ x*linearRadiusHessian A v w x) =
      ∫ x, fderiv ℝ (fun y => fderiv ℝ φ y w) x v*‖A x‖ := by
  have hbc : LocallyIntegrable (fun x => (2*‖A v‖*‖A w‖)*‖A x‖⁻¹) volume := by
    simpa only [Pi.smul_def,smul_eq_mul] using hb.smul (2*‖A v‖*‖A w‖)
  have hd (n : ℕ) : ContDiff ℝ ∞
      (fun y => fderiv ℝ (regularizedLinearRadius A (radiusRegularization n)) y v) :=
    ((regularizedLinearRadius_contDiff A (radiusRegularization_pos n)).fderiv_right
      (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  have hl := compact_real_test_integral_tendsto_locally_dominated hbc
    (fun n => ((hd n).continuous_fderiv (by simp)).clm_apply
      (continuous_const : Continuous (fun _ : Configuration N => w)) |>.aestronglyMeasurable)
    (fun n => by
      filter_upwards [hne] with x hx
      simp only [Real.norm_eq_abs]
      rw [abs_of_nonneg (by positivity : 0 ≤ 2*‖A v‖*‖A w‖*‖A x‖⁻¹)]
      simpa only [div_eq_mul_inv] using
        regularizedLinearRadius_mixed_coulomb_bound A (radiusRegularization_pos n) hx v w)
    (by
      filter_upwards [hne] with x hx
      exact regularizedLinearRadius_hessian_tendsto A radiusRegularization_pos
        radiusRegularization_tendsto hx v w)
    hφ.continuous hc
  have hdφ : ContDiff ℝ ∞ (fun y => fderiv ℝ φ y w) :=
    (hφ.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  have htest : Continuous (fun x => fderiv ℝ (fun y => fderiv ℝ φ y w) x v) :=
    (hdφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hbF : LocallyIntegrable (fun x : Configuration N => ‖A x‖+1) volume :=
    (A.continuous.norm.add continuous_const).locallyIntegrable
  have hr := compact_real_test_integral_tendsto_locally_dominated hbF
    (fun n => (regularizedLinearRadius_contDiff A (radiusRegularization_pos n)).continuous.aestronglyMeasurable)
    (fun n => by
      filter_upwards with x
      rw [Real.norm_eq_abs,Real.norm_eq_abs,
        abs_of_pos (regularizedLinearRadius_pos A (radiusRegularization_pos n) x),
        abs_of_nonneg (by positivity : 0 ≤ ‖A x‖+1)]
      exact regularizedLinearRadius_le_norm_add_one A (radiusRegularization_pos n)
        (radiusRegularization_le_one n) x)
    (Eventually.of_forall (fun x => regularizedLinearRadius_tendsto A radiusRegularization_tendsto x))
    htest ((hc.fderiv_apply ℝ w).fderiv_apply ℝ v)
  have he (n : ℕ) := configuration_integral_mixed_transfer hφ
    (regularizedLinearRadius_contDiff A (radiusRegularization_pos n)) hc v w
  exact tendsto_nhds_unique hl (hr.congr' (Eventually.of_forall (fun n => (he n).symm)))

#print axioms linear_radius_weak_hessian_test
end TheoremT.Continuum
