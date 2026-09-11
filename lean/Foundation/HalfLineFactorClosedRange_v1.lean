import HalfLineFactors_v1
import Mathlib.Analysis.Normed.Operator.Banach

/-! The actual partner B has closed range and controls the full declared
half-line domain norm. A value-only estimate would not suffice for this step. -/
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Set Filter
open scoped Topology
namespace TheoremT.HalfLine

def gapRoot (Z : ℝ) : ℝ := Real.sqrt (3 * Z^2 / 4)

theorem gapRoot_pos {Z : ℝ} (hZ : 0 < Z) : 0 < gapRoot Z := by
  unfold gapRoot
  positivity

theorem gapRoot_sq (Z : ℝ) : (gapRoot Z)^2 = 3 * Z^2 / 4 := by
  exact Real.sq_sqrt (by positivity)

theorem value_norm_B (Z : ℝ) (u : D) : gapRoot Z * ‖J u‖ ≤ ‖B Z u‖ := by
  have h := value_coercivity_B Z u
  have hs := gapRoot_sq Z
  have hp : 0 ≤ gapRoot Z := Real.sqrt_nonneg _
  nlinarith [norm_nonneg (J u), norm_nonneg (B Z u)]

theorem full_domain_bound_B {Z : ℝ} (hZ : 0 < Z) (u : D) :
    ‖u‖ ≤ (1 + (gapRoot Z)⁻¹) * ‖B Z u‖ := by
  have hc := gapRoot_pos hZ
  have h0 : 0 ≤ (gapRoot Z)⁻¹ := inv_nonneg.mpr hc.le
  have hv : ‖J u‖ ≤ (gapRoot Z)⁻¹ * ‖B Z u‖ := by
    have h := mul_le_mul_of_nonneg_left (value_norm_B Z u) h0
    simpa only [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] using h
  rw [domain_norm]
  apply max_le
  · nlinarith [norm_nonneg (B Z u)]
  · have hd := derivative_bound_B Z u
    have hh := mul_nonneg h0 (norm_nonneg (B Z u))
    nlinarith

theorem B_antilipschitz {Z : ℝ} (hZ : 0 < Z) :
    AntilipschitzWith (⟨1 + (gapRoot Z)⁻¹, by unfold gapRoot; positivity⟩ : NNReal) (B Z) :=
  (B Z).antilipschitz_of_bound (full_domain_bound_B hZ)

theorem B_injective {Z : ℝ} (hZ : 0 < Z) : Function.Injective (B Z) :=
  (B_antilipschitz hZ).injective

theorem B_range_closed {Z : ℝ} (hZ : 0 < Z) :
    (B Z).range.topologicalClosure = (B Z).range :=
  ContinuousLinearMap.closed_range_of_antilipschitz (B_antilipschitz hZ)

#print axioms value_norm_B
#print axioms full_domain_bound_B
#print axioms B_injective
#print axioms B_range_closed
end TheoremT.HalfLine
