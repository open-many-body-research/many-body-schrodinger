import ConfigurationLocalDominated_v1
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Rescaled integrable kernels against bounded continuous tests. The proof
uses Haar change of variables and dominated convergence, not a point-mass axiom. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace TheoremT.Continuum

theorem integrable_kernel_dilation_test_tendsto {N : ℕ} {K : Configuration N → ℝ}
    (hK : Integrable K volume) {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    {φ : Configuration N → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    Tendsto (fun n => ∫ y, K y*φ (ε n • y)) atTop (𝓝 ((∫ y, K y)*φ 0)) := by
  obtain ⟨C,hC⟩ := hφ.bounded_above_of_compact_support hc
  have hD := tendsto_integral_of_dominated_convergence
    (F := fun n y => K y*φ (ε n • y)) (f := fun y => K y*φ 0) (fun y => ‖K y‖*C)
    (fun n => hK.aestronglyMeasurable.mul
      (show Continuous (fun y => φ (ε n • y)) from hφ.comp (continuous_id.const_smul (ε n))).aestronglyMeasurable)
    (hK.norm.mul_const C)
    (fun n => Eventually.of_forall (fun y => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)))
    (Eventually.of_forall (fun y => tendsto_const_nhds.mul ((hφ.continuousAt.tendsto).comp
      (by simpa using hε.smul_const y))))
  simpa only [integral_mul_const] using hD

#print axioms integrable_kernel_dilation_test_tendsto
end TheoremT.Continuum
