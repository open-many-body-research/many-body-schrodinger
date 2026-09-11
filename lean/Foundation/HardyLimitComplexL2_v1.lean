import HardyLimitComplex_v1

/-! Actual complex L² multiplier consequence of compact C¹ Hardy. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace TheoremT.Hardy

/-- The physical inverse-distance multiplier maps every complex compact C¹
function on R³ to L², with the Hardy norm-square bound. -/
theorem complex_hardy_memLp_two_and_bound {u : R3 → ℂ}
    (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u) :
    MemLp (fun x => u x / (‖x‖ : ℂ)) 2 volume ∧
      (∫ x, ‖u x / (‖x‖ : ℂ)‖^2) ≤
        4 * (∫ x, ∑ i : Fin 3, ‖fderiv ℝ u x (basisVector i)‖^2) := by
  have h := complex_hardy_integrable_sq_and_bound hu huc
  have hm : AEStronglyMeasurable (fun x : R3 => u x / (‖x‖ : ℂ)) volume :=
    (hu.continuous.measurable.div
      (Complex.ofRealCLM.continuous.comp continuous_norm).measurable).aestronglyMeasurable
  constructor
  · apply (memLp_two_iff_integrable_sq_norm hm).2
    simpa only [norm_div, Complex.norm_real, norm_norm, div_pow] using h.1
  · simpa only [norm_div, Complex.norm_real, norm_norm, div_pow] using h.2

set_option pp.proofs false in
#print complex_hardy_memLp_two_and_bound
#print axioms complex_hardy_memLp_two_and_bound
end TheoremT.Hardy
