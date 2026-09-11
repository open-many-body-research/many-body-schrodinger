import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

/-! The probability-average L² estimate needed for normalized mollifier contraction.
This is an unconditional Jensen consequence, not an assumption of Young's inequality. -/
noncomputable section
open MeasureTheory
namespace TheoremT.HardyConvolution

/-- Every square-integrable Banach-valued random variable has squared mean norm
bounded by its mean squared norm. Both integral existence claims are discharged. -/
theorem norm_integral_sq_le_integral_norm_sq
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure α} [IsProbabilityMeasure μ] {f : α → E}
    (hf : MemLp f 2 μ) :
    ‖∫ x, f x ∂μ‖^2 ≤ ∫ x, ‖f x‖^2 ∂μ := by
  have hconv : ConvexOn ℝ Set.univ (fun x : E => ‖x‖^2) :=
    convexOn_univ_norm.pow (fun x _ => norm_nonneg x) 2
  exact hconv.map_integral_le (continuous_norm.pow 2).continuousOn
    isClosed_univ (Filter.Eventually.of_forall (fun _ => Set.mem_univ _))
    (hf.integrable (by norm_num)) (hf.integrable_norm_pow (by norm_num))

set_option pp.proofs false in
#print norm_integral_sq_le_integral_norm_sq
#print axioms norm_integral_sq_le_integral_norm_sq
end TheoremT.HardyConvolution
