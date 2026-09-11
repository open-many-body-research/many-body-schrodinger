import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Tactic

/-! Actual integral-square continuity for uniform limits on a compact space
with finite Borel measure. All integrability and limit passage are proved;
this is used with the genuine sphere area measure in the angular theorem. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace TheoremT.HydrogenSphereC1Limit

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]

def continuousMapIntegral : C(X, ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x, f x ∂μ
      map_add' := fun f g => integral_add
        (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      map_smul' := fun c f => by simp [integral_const_mul] }
    (μ.real Set.univ) (fun f => by
      change ‖∫ x, f x ∂μ‖ ≤ μ.real Set.univ * ‖f‖
      simpa only [mul_comm] using norm_integral_le_of_norm_le_const
        (Filter.Eventually.of_forall (fun x => ContinuousMap.norm_coe_le_norm f x)))

theorem continuousMapIntegral_apply (f : C(X, ℝ)) :
    continuousMapIntegral μ f = ∫ x, f x ∂μ := rfl

theorem integral_of_continuousMap_limit {F : ℕ → C(X, ℝ)} {f : C(X, ℝ)}
    (hf : Tendsto F atTop (𝓝 f)) :
    Tendsto (fun n => ∫ x, F n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) :=
  (continuousMapIntegral μ).continuous.tendsto f |>.comp hf

theorem integral_square_of_continuousMap_limit {F : ℕ → C(X, ℝ)} {f : C(X, ℝ)}
    (hf : Tendsto F atTop (𝓝 f)) :
    Tendsto (fun n => ∫ x, (F n x) ^ 2 ∂μ) atTop (𝓝 (∫ x, (f x) ^ 2 ∂μ)) := by
  simpa only [ContinuousMap.mul_apply, pow_two] using
    integral_of_continuousMap_limit μ (hf.mul hf)

def centerContinuousMap (c : ℝ) (f : C(X, ℝ)) : C(X, ℝ) :=
  f - ContinuousMap.const X ((∫ x, f x ∂μ) / c)

theorem centerContinuousMap_limit (c : ℝ) {F : ℕ → C(X, ℝ)} {f : C(X, ℝ)}
    (hf : Tendsto F atTop (𝓝 f)) :
    Tendsto (fun n => centerContinuousMap μ c (F n)) atTop (𝓝 (centerContinuousMap μ c f)) := by
  exact hf.sub (ContinuousMap.continuous_const'.tendsto _ |>.comp
    ((integral_of_continuousMap_limit μ hf).div_const c))

theorem integral_centered_square_of_continuousMap_limit (c : ℝ)
    {F : ℕ → C(X, ℝ)} {f : C(X, ℝ)} (hf : Tendsto F atTop (𝓝 f)) :
    Tendsto
      (fun n => ∫ x, (F n x - (∫ y, F n y ∂μ) / c) ^ 2 ∂μ) atTop
      (𝓝 (∫ x, (f x - (∫ y, f y ∂μ) / c) ^ 2 ∂μ)) := by
  simpa only [centerContinuousMap, ContinuousMap.sub_apply, ContinuousMap.const_apply] using
    integral_square_of_continuousMap_limit μ (centerContinuousMap_limit μ c hf)

end TheoremT.HydrogenSphereC1Limit

#print axioms TheoremT.HydrogenSphereC1Limit.integral_square_of_continuousMap_limit
#print axioms TheoremT.HydrogenSphereC1Limit.integral_centered_square_of_continuousMap_limit
