import HalfLineRangeExact_v1
import HalfLineValueDensity_v1

/-! The kernel of the actual first-order factor is determined by the explicit
radial ground profile, without assuming the profile's domain membership. -/
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Set Filter
open scoped Topology
namespace TheoremT.HalfLine

theorem A_zero_iff_J_orthogonal_range (Z : ℝ) (u : D) :
    A Z u = 0 ↔ J u ∈ (B Z).range.orthogonal := by
  constructor
  · intro hu
    rintro _ ⟨v,rfl⟩
    change inner ℂ (B Z v) (J u) = 0
    have h := factor_pairing Z u v
    rw [hu, inner_zero_left] at h
    rw [← inner_conj_symm]
    rw [← h]
    simp
  · intro hu
    have hz : A Z u ∈ J.range.orthogonal := by
      rintro _ ⟨v,rfl⟩
      change inner ℂ (J v) (A Z u) = 0
      have h := hu (B Z v) (LinearMap.mem_range_self (B Z).toLinearMap v)
      rw [← inner_conj_symm]
      rw [factor_pairing, ← inner_conj_symm, h]
      simp
    rw [J_range_orthogonal] at hz
    exact hz

theorem A_zero_iff_J_ground_span (Z : ℝ) (hZ : 0 < Z) (u : D) :
    A Z u = 0 ↔ J u ∈ Submodule.span ℂ {radialGroundL2 Z hZ} := by
  rw [A_zero_iff_J_orthogonal_range, range_orthogonal_eq_ground_span Z hZ]

theorem A_zero_iff_J_ground_multiple (Z : ℝ) (hZ : 0 < Z) (u : D) :
    A Z u = 0 ↔ ∃ c : ℂ, c • radialGroundL2 Z hZ = J u := by
  rw [A_zero_iff_J_ground_span, Submodule.mem_span_singleton]

#print axioms A_zero_iff_J_orthogonal_range
#print axioms A_zero_iff_J_ground_span
#print axioms A_zero_iff_J_ground_multiple
end TheoremT.HalfLine
