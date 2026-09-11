import HalfLineGroundFactor_v1
import HalfLineHydrogenComplement_v1

/-! An actual rank-one comparison on every vector in the declared half-line
domain. The rank-one vector is the normalized physical ground profile. -/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter
open scoped Topology
namespace TheoremT.HalfLine

def groundCoefficient (Z : ℝ) (hZ : 0 < Z) (u : D) : ℂ :=
  inner ℂ (normalizedGround Z hZ) (J u)

def groundRemainder (Z : ℝ) (hZ : 0 < Z) (u : D) : D :=
  u - groundCoefficient Z hZ u • normalizedGroundD Z hZ

theorem J_groundRemainder (Z : ℝ) (hZ : 0 < Z) (u : D) :
    J (groundRemainder Z hZ u) = J u - groundCoefficient Z hZ u • normalizedGround Z hZ := by
  simp only [groundRemainder, map_sub, map_smul, normalizedGround]

theorem groundRemainder_orthogonal_normalized (Z : ℝ) (hZ : 0 < Z) (u : D) :
    inner ℂ (normalizedGround Z hZ) (J (groundRemainder Z hZ u)) = 0 := by
  rw [J_groundRemainder, inner_sub_right, inner_smul_right, normalizedGround_inner_self,
    mul_one]
  exact sub_self _

theorem groundRemainder_orthogonal (Z : ℝ) (hZ : 0 < Z) (u : D) :
    inner ℂ (radialGroundL2 Z hZ) (J (groundRemainder Z hZ u)) = 0 := by
  rw [radialGround_eq_norm_smul, inner_smul_left, groundRemainder_orthogonal_normalized, mul_zero]

theorem A_groundRemainder (Z : ℝ) (hZ : 0 < Z) (u : D) :
    A Z (groundRemainder Z hZ u) = A Z u := by
  simp only [groundRemainder, map_sub, map_smul, A_normalizedGroundD, smul_zero, sub_zero]

theorem groundRemainder_norm_sq (Z : ℝ) (hZ : 0 < Z) (u : D) :
    ‖J (groundRemainder Z hZ u)‖^2 = ‖J u‖^2 - ‖groundCoefficient Z hZ u‖^2 := by
  rw [J_groundRemainder, norm_sub_sq (𝕜 := ℂ), inner_smul_right,
    _root_.norm_smul, normalizedGround_norm, mul_one]
  have hi : inner ℂ (J u) (normalizedGround Z hZ) = star (groundCoefficient Z hZ u) := by
    exact (inner_conj_symm _ _).symm
  rw [hi]
  change ‖J u‖^2 - 2 * (groundCoefficient Z hZ u * star (groundCoefficient Z hZ u)).re +
    ‖groundCoefficient Z hZ u‖^2 = _
  rw [RCLike.star_def, RCLike.mul_conj]
  change ‖J u‖^2 - 2 * ((‖groundCoefficient Z hZ u‖ : ℂ)^2).re +
    ‖groundCoefficient Z hZ u‖^2 = _
  rw [← Complex.ofReal_pow, Complex.ofReal_re]
  ring

theorem q_groundRemainder (Z : ℝ) (hZ : 0 < Z) (u : D) :
    q Z (groundRemainder Z hZ u) = q Z u + (Z^2/2) * ‖groundCoefficient Z hZ u‖^2 := by
  rw [q_square_A, q_square_A, A_groundRemainder, groundRemainder_norm_sq]
  ring

theorem hydrogen_radial_rank_one (Z : ℝ) (hZ : 0 < Z) (u : D) :
    -(Z^2/8) * ‖J u‖^2 - (3*Z^2/8) * ‖inner ℂ (normalizedGround Z hZ) (J u)‖^2 ≤ q Z u := by
  have h := hydrogen_radial_complement Z hZ (groundRemainder Z hZ u)
    (groundRemainder_orthogonal Z hZ u)
  rw [groundRemainder_norm_sq, q_groundRemainder] at h
  change -(Z^2/8) * ‖J u‖^2 - (3*Z^2/8) * ‖groundCoefficient Z hZ u‖^2 ≤ q Z u
  nlinarith

theorem hydrogen_radial_rank_one_integral (Z : ℝ) (hZ : 0 < Z) (u : D) :
    -(Z^2/8) * ‖J u‖^2 - (3*Z^2/8) * ‖inner ℂ (normalizedGround Z hZ) (J u)‖^2 ≤
      (1/2) * ‖dJ u‖^2 - Z * ∫ x, ‖J u x‖^2 / x ∂μ := by
  rw [← q_physical]
  exact hydrogen_radial_rank_one Z hZ u

#print axioms groundCoefficient
#print axioms groundRemainder
#print axioms J_groundRemainder
#print axioms groundRemainder_orthogonal_normalized
#print axioms groundRemainder_orthogonal
#print axioms A_groundRemainder
#print axioms groundRemainder_norm_sq
#print axioms q_groundRemainder
#print axioms hydrogen_radial_rank_one
#print axioms hydrogen_radial_rank_one_integral
end TheoremT.HalfLine
