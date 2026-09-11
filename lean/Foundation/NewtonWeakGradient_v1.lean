import NewtonGradientIntegrability_v1
import NewtonFundamentalSolution_v1

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace TheoremT.Continuum

theorem regularizedNewtonPotential_test_tendsto {N : ℕ} (hN : 0 < N)
    {φ : Configuration N → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    Tendsto (fun n => ∫ x, φ x*regularizedNewtonPotential N (radiusRegularization n) x) atTop
      (𝓝 (∫ x, φ x*newtonPotential N x)) := by
  apply compact_real_test_integral_tendsto_locally_dominated (newtonPotential_locallyIntegrable hN)
    (fun n => (regularizedNewtonPotential_contDiff N (radiusRegularization_pos n)).continuous.aestronglyMeasurable)
    _ _ hφ hc
  · intro n
    filter_upwards [configuration_ae_ne_zero hN] with x hx
    simpa only [Real.norm_eq_abs,newtonPotential,abs_mul,
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _)] using
      regularizedNewtonPotential_abs_bound hN (radiusRegularization_pos n) hx
  · filter_upwards [configuration_ae_ne_zero hN] with x hx
    exact regularizedNewtonPotential_tendsto radiusRegularization_tendsto hx

theorem newtonPotential_weak_partial_test {N : ℕ} (hN : 0 < N) (k : Coordinate N)
    {φ : Configuration N → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∫ x, φ x*newtonGradient N k x) =
      -(∫ x, fderiv ℝ φ x (coordinateVector k)*newtonPotential N x) := by
  have hb : LocallyIntegrable (fun x : Configuration N => ‖x‖^(1-(3*N:ℝ))) volume := by
    simpa only [neg_sub] using configuration_norm_rpow_locallyIntegrable hN
      (α := (3*N:ℝ)-1) (by linarith)
  have hlim := compact_real_test_integral_tendsto_locally_dominated hb
    (fun n => (((regularizedNewtonPotential_contDiff N (radiusRegularization_pos n)).continuous_fderiv
      (by simp)).clm_apply continuous_const).aestronglyMeasurable)
    (fun n => by
      filter_upwards [configuration_ae_ne_zero hN] with x hx
      simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _)] using
        regularizedNewtonGradient_abs_bound hN (radiusRegularization_pos n) hx k)
    (by
      filter_upwards [configuration_ae_ne_zero hN] with x hx
      exact regularizedNewtonGradient_tendsto hN radiusRegularization_pos radiusRegularization_tendsto hx k)
    hφ.continuous hc
  have hD := regularizedNewtonPotential_test_tendsto hN
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const) (hc.fderiv_apply ℝ (coordinateVector k))
  have he (n : ℕ) := configuration_integral_mul_fderiv_compact (hφ.of_le (by simp))
    ((regularizedNewtonPotential_contDiff N (radiusRegularization_pos n)).of_le (by simp)) hc (coordinateVector k)
  exact tendsto_nhds_unique hlim (hD.neg.congr' (Eventually.of_forall (fun n => (he n).symm)))

def normalizedNewtonGradient (N : ℕ) (k : Coordinate N) (x : Configuration N) : ℝ :=
  (newtonMass N)⁻¹*newtonGradient N k x

theorem normalizedNewtonPotential_weak_partial_test {N : ℕ} (hN : 0 < N) (k : Coordinate N)
    {φ : Configuration N → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∫ x, φ x*normalizedNewtonGradient N k x) =
      -(∫ x, fderiv ℝ φ x (coordinateVector k)*normalizedNewtonPotential N x) := by
  simp only [normalizedNewtonGradient,normalizedNewtonPotential,mul_left_comm (φ _) (newtonMass N)⁻¹,
    mul_left_comm (fderiv ℝ φ _ _) (newtonMass N)⁻¹,integral_const_mul]
  rw [newtonPotential_weak_partial_test hN k hφ hc]
  ring

#print axioms normalizedNewtonPotential_weak_partial_test
end TheoremT.Continuum
