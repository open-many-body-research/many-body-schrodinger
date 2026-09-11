import ConfigurationSmoothGreen_v1
import AtomicSobolevExponent_v1
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Compact-test limits with locally integrable bounds, including the true
inverse radius on configuration space. No global integrability of a radius
or its reciprocal is assumed. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace TheoremT.Continuum

theorem configuration_inverse_radius_locallyIntegrable {N : ℕ} (hN : 0 < N) :
    LocallyIntegrable (fun x : Configuration N => ‖x‖⁻¹) volume := by
  apply locallyIntegrable_of_norm_le_rpow (C := 1) (α := 1)
    (by rw [configuration_finrank]; omega)
    (by rw [configuration_finrank]; exact_mod_cast (show 1 < 3*N by omega))
  · filter_upwards with x
    simp [Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)),Real.rpow_neg_one]
  · exact continuous_norm.measurable.inv.aestronglyMeasurable

theorem compact_real_test_integral_tendsto_locally_dominated {N : ℕ}
    {u : ℕ → Configuration N → ℝ} {f bound : Configuration N → ℝ}
    (hb : LocallyIntegrable bound volume)
    (hu : ∀ n, AEStronglyMeasurable (u n) volume)
    (hbound : ∀ n, ∀ᵐ x, ‖u n x‖ ≤ ‖bound x‖)
    (hlim : ∀ᵐ x, Tendsto (fun n => u n x) atTop (𝓝 (f x)))
    {φ : Configuration N → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    Tendsto (fun n => ∫ x, φ x*u n x) atTop (𝓝 (∫ x, φ x*f x)) := by
  have hbi : Integrable (fun x => ‖φ x‖*‖bound x‖) volume := by
    have hbn : LocallyIntegrable (fun x => ‖bound x‖) volume := by
      rw [locallyIntegrable_iff]
      intro K hK
      exact (hb.integrableOn_isCompact hK).norm
    simpa only [smul_eq_mul] using hbn.integrable_smul_left_of_hasCompactSupport hφ.norm hc.norm
  apply tendsto_integral_of_dominated_convergence (fun x => ‖φ x‖*‖bound x‖)
  · intro n; exact hφ.aestronglyMeasurable.mul (hu n)
  · exact hbi
  · intro n
    filter_upwards [hbound n] with x hx
    simpa only [norm_mul] using mul_le_mul_of_nonneg_left hx (norm_nonneg (φ x))
  · filter_upwards [hlim] with x hx
    exact tendsto_const_nhds.mul hx

#print axioms configuration_inverse_radius_locallyIntegrable
#print axioms compact_real_test_integral_tendsto_locally_dominated
end TheoremT.Continuum
