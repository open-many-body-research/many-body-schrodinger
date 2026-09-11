import HardyLimitCompact_v1

/-! The multiplier conclusion of the regularized Hardy limit bridge.
The bound on regularized integrals remains explicit. -/
noncomputable section
open MeasureTheory
namespace TheoremT.HardyLimit

/-- Under regularized Hardy bounds, multiplication by `1/‖x‖` belongs to actual
Lebesgue `L²`; this is not inferred from a possibly totalized Bochner integral. -/
theorem inverseNorm_memLp_of_regularized_bounds {u : R3 → ℝ} {B : ℝ}
    (hu : Continuous u) (huc : HasCompactSupport u)
    (hbound : ∀ δ : ℝ, 0 < δ → (∫ x, (u x)^2 / (‖x‖^2 + δ)) ≤ B) :
    MemLp (fun x => u x / ‖x‖) 2 volume ∧
      (∫ x, (u x / ‖x‖)^2) ≤ B := by
  have h := singularWeight_of_regularized_bounds hu huc hbound
  have hm : AEStronglyMeasurable (fun x : R3 => u x / ‖x‖) volume :=
    (hu.measurable.div continuous_norm.measurable).aestronglyMeasurable
  constructor
  · apply (memLp_two_iff_integrable_sq hm).2
    simpa only [div_pow] using h.1
  · simpa only [div_pow] using h.2

#print inverseNorm_memLp_of_regularized_bounds
#print axioms inverseNorm_memLp_of_regularized_bounds
end TheoremT.HardyLimit
