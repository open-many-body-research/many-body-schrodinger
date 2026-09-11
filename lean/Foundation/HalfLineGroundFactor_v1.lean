import HalfLineFactorKernel_v1
import HalfLineGroundDomain_v1
import HalfLineHydrogenNonzero_v1
import HalfLinePhysicalForm_v1

/-! The actual normalized radial ground vector lies in the compact H1 closure,
annihilates the first-order factor, and attains its ground form value. -/
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Set Filter
open scoped Topology
namespace TheoremT.HalfLine

theorem A_radialGroundD (Z : ℝ) (hZ : 0 < Z) : A Z (radialGroundD Z hZ) = 0 := by
  apply (A_zero_iff_J_ground_multiple Z hZ _).mpr
  exact ⟨1, by rw [one_smul, J_radialGroundD]⟩

def normalizedGroundD (Z : ℝ) (hZ : 0 < Z) : D :=
  (‖radialGroundL2 Z hZ‖⁻¹ : ℂ) • radialGroundD Z hZ

def normalizedGround (Z : ℝ) (hZ : 0 < Z) : E := J (normalizedGroundD Z hZ)

theorem normalizedGround_eq (Z : ℝ) (hZ : 0 < Z) :
    normalizedGround Z hZ = (‖radialGroundL2 Z hZ‖⁻¹ : ℂ) • radialGroundL2 Z hZ := by
  simp only [normalizedGround, normalizedGroundD, map_smul, J_radialGroundD]

theorem normalizedGround_norm (Z : ℝ) (hZ : 0 < Z) : ‖normalizedGround Z hZ‖ = 1 := by
  rw [normalizedGround_eq, _root_.norm_smul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀]
  exact norm_ne_zero_iff.mpr (radialGroundL2_ne_zero Z hZ)

theorem A_normalizedGroundD (Z : ℝ) (hZ : 0 < Z) : A Z (normalizedGroundD Z hZ) = 0 := by
  simp only [normalizedGroundD, map_smul, A_radialGroundD, smul_zero]

theorem radialGround_eq_norm_smul (Z : ℝ) (hZ : 0 < Z) :
    radialGroundL2 Z hZ = (‖radialGroundL2 Z hZ‖ : ℂ) • normalizedGround Z hZ := by
  rw [normalizedGround_eq, smul_smul]
  have hn := norm_ne_zero_iff.mpr (radialGroundL2_ne_zero Z hZ)
  have hc : (‖radialGroundL2 Z hZ‖ : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [mul_inv_cancel₀ hc, one_smul]

theorem normalizedGround_inner_self (Z : ℝ) (hZ : 0 < Z) :
    inner ℂ (normalizedGround Z hZ) (normalizedGround Z hZ) = 1 := by
  rw [inner_self_eq_norm_sq_to_K, normalizedGround_norm]
  norm_num

theorem q_normalizedGroundD (Z : ℝ) (hZ : 0 < Z) :
    q Z (normalizedGroundD Z hZ) = -(Z^2/2) := by
  rw [q_square_A, A_normalizedGroundD]
  change (1/2) * ‖(0 : E)‖^2 - Z^2/2 * ‖normalizedGround Z hZ‖^2 = _
  rw [normalizedGround_norm]
  simp

theorem normalizedGround_physical_energy (Z : ℝ) (hZ : 0 < Z) :
    (1/2) * ‖dJ (normalizedGroundD Z hZ)‖^2 -
      Z * ∫ x, ‖normalizedGround Z hZ x‖^2 / x ∂μ = -(Z^2/2) := by
  exact (q_physical Z (normalizedGroundD Z hZ)).symm.trans (q_normalizedGroundD Z hZ)

#print axioms A_radialGroundD
#print axioms normalizedGroundD
#print axioms normalizedGround
#print axioms normalizedGround_eq
#print axioms normalizedGround_norm
#print axioms A_normalizedGroundD
#print axioms radialGround_eq_norm_smul
#print axioms normalizedGround_inner_self
#print axioms q_normalizedGroundD
#print axioms normalizedGround_physical_energy
end TheoremT.HalfLine
