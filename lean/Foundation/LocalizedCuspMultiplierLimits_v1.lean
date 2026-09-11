import RegularizedLocalizedCusp_v1
import BoundedRealMultiplierLimit_v1
import CoulombCuspHessianProduct_v1

noncomputable section
open MeasureTheory Filter
open scoped ContDiff Topology
namespace TheoremT.Continuum

theorem localizedCusp_value_multiplier_limit (N : ℕ) (Z : ℝ)
    {χ : Configuration N → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    ∃ h₀ : MemLp (localizedCusp N Z χ) (⊤ : ENNReal) volume, ∀ f : SpatialL2 N,
      Tendsto (fun n => boundedRealMul (regularizedLocalizedCusp N Z χ n)
        (regularizedLocalizedCusp_memLp_top N Z hχ hc n) f) atTop
        (𝓝 (boundedRealMul (localizedCusp N Z χ) h₀ f)) := by
  obtain ⟨C,hC0,hC⟩ := localized_cusp_regularization_bound N Z hχ.continuous hc
  apply bounded_real_multiplier_limit _ C hC0
  · intro n
    filter_upwards with x
    simpa only [Real.norm_eq_abs, regularizedLocalizedCusp] using hC (radiusRegularization n) (radiusRegularization_pos n)
      (radiusRegularization_le_one n) x
  · exact Eventually.of_forall (fun x => localizedCusp_value_tendsto N Z χ x)

theorem localizedCusp_gradient_multiplier_limit (N : ℕ) (Z : ℝ)
    {χ : Configuration N → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (v : Configuration N) :
    ∃ h₀ : MemLp (localizedCuspGradient N Z χ v) (⊤ : ENNReal) volume, ∀ f : SpatialL2 N,
      Tendsto (fun n => boundedRealMul (fun x => fderiv ℝ (regularizedLocalizedCusp N Z χ n) x v)
        (regularizedLocalizedCusp_partial_memLp_top N Z hχ hc n v) f) atTop
        (𝓝 (boundedRealMul (localizedCuspGradient N Z χ v) h₀ f)) := by
  obtain ⟨C,hC0,hC⟩ := localized_cusp_partial_uniform_bound N Z hχ hc v
  apply bounded_real_multiplier_limit _ C hC0
  · intro n
    filter_upwards with x
    change ‖fderiv ℝ (fun y => χ y * Real.exp (-regularizedCoulombCusp N Z (radiusRegularization n) y)) x v‖ ≤ C
    rw [Real.norm_eq_abs]
    exact hC (radiusRegularization n) (radiusRegularization_pos n) (radiusRegularization_le_one n) x
  · filter_upwards [ae_collisionFree N] with x hx
    exact localizedCusp_gradient_tendsto N Z hχ hx v

theorem localizedCusp_hessian_multiplier_limit (N : ℕ) (Z : ℝ)
    {χ : Configuration N → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (v w : Configuration N) (f : SpatialL2 N) (hf : HasH1 f) :
    ∃ h₀ : MemLp (fun x => localizedCuspHessian N Z χ v w x • f x) 2 volume,
      Tendsto (fun n => boundedRealMul (fun x => fderiv ℝ
        (fun y => fderiv ℝ (regularizedLocalizedCusp N Z χ n) y v) x w)
        (regularizedLocalizedCusp_mixed_memLp_top N Z hχ hc n v w) f) atTop
        (𝓝 (h₀.toLp (fun x => localizedCuspHessian N Z χ v w x • f x))) := by
  obtain ⟨M,C,hM0,hC0,hB⟩ := localized_cusp_mixed_uniform_coulomb_bound N Z hχ hc v w
  have hmb : MemLp (fun x => (M+C*cuspHessianBound N Z v w x)*‖f x‖) 2 volume := by
    have h := ((Lp.memLp f).norm.const_mul M).add ((cuspHessianBound_mul_memLp Z v w hf).const_mul C)
    apply h.ae_eq
    filter_upwards with x
    simp only [Pi.add_apply,add_mul,mul_assoc]
  apply dominated_real_multiplier_limit f _ hmb
  · intro n
    filter_upwards [ae_collisionFree N] with x hx
    have hH := cuspHessianBound_nonneg N Z v w x
    rw [Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ M+C*cuspHessianBound N Z v w x)]
    exact hB (radiusRegularization n) (radiusRegularization_pos n) (radiusRegularization_le_one n) x hx
  · filter_upwards [ae_collisionFree N] with x hx
    exact localizedCusp_hessian_tendsto N Z hχ hx v w

#print axioms localizedCusp_value_multiplier_limit
#print axioms localizedCusp_gradient_multiplier_limit
#print axioms localizedCusp_hessian_multiplier_limit
end TheoremT.Continuum
