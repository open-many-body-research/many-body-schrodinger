import HalfLineRangeExact_v1
import HalfLinePhysicalForm_v1
import PartnerGapTransfer_v1

/-! The actual half-line hydrogen complement bound. Its only hypotheses are
positive charge, membership in the declared compact H¹₀ graph closure, and
orthogonality to the explicit radial ground profile. -/
noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory Set Filter
open scoped Topology
namespace TheoremT.HalfLine

theorem hydrogen_radial_factor_gap (Z : ℝ) (hZ : 0 < Z) (u : D)
    (hu : inner ℂ (radialGroundL2 Z hZ) (J u) = 0) :
    gapRoot Z * ‖J u‖ ≤ ‖A Z u‖ := by
  have hK : 0 < 1 + (gapRoot Z)⁻¹ := by
    have hpos := gapRoot_pos hZ
    positivity
  exact OperatorTheory.partner_gap_transfer J (A Z) (B Z)
    (1 + (gapRoot Z)⁻¹) (gapRoot Z) hK (gapRoot_pos hZ)
    (full_domain_bound_B hZ) (value_norm_B Z) (factor_pairing Z)
    (radialGroundL2 Z hZ) (range_orthogonal_eq_ground_span Z hZ) u hu

theorem hydrogen_radial_complement (Z : ℝ) (hZ : 0 < Z) (u : D)
    (hu : inner ℂ (radialGroundL2 Z hZ) (J u) = 0) :
    -(Z^2/8) * ‖J u‖^2 ≤ q Z u := by
  have hn := hydrogen_radial_factor_gap Z hZ u hu
  have hs := mul_self_le_mul_self
    (mul_nonneg (gapRoot_pos hZ).le (norm_nonneg (J u))) hn
  simp only [← pow_two, mul_pow, gapRoot_sq] at hs
  rw [q_square_A]
  nlinarith

theorem hydrogen_radial_complement_integral (Z : ℝ) (hZ : 0 < Z) (u : D)
    (hu : inner ℂ (radialGroundL2 Z hZ) (J u) = 0) :
    -(Z^2/8) * ‖J u‖^2 ≤
      (1/2) * ‖dJ u‖^2 - Z * ∫ x, ‖J u x‖^2 / x ∂μ := by
  rw [← q_physical]
  exact hydrogen_radial_complement Z hZ u hu

#print axioms hydrogen_radial_factor_gap
#print axioms hydrogen_radial_complement
#print axioms hydrogen_radial_complement_integral
end TheoremT.HalfLine
