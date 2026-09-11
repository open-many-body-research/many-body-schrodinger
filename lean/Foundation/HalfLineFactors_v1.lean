import HalfLineDomainPairing_v1
import HalfLineThreeSquareAlgebra_v1

/-! The actual half-line Coulomb first-order factors on exactly the declared
closed H¹₀ graph domain. Square identities and graph estimates hold for every
input, with all compact integration premises discharged. -/
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Set Filter
open scoped Topology
namespace TheoremT.HalfLine

def A (Z : ℝ) : D →L[ℂ] E := dJ - W + Z • J
def B (Z : ℝ) : D →L[ℂ] E := -dJ - W + Z • J
def C (Z : ℝ) : D →L[ℂ] E := dJ - (2:ℝ) • W + (Z/2) • J

def coulombMoment (u : D) : ℝ := inner ℝ (W u) (J u)
def q (Z : ℝ) (u : D) : ℝ := (1/2) * ‖dJ u‖^2 - Z * coulombMoment u

theorem A_apply (Z : ℝ) (u : D) : A Z u = dJ u - W u + Z • J u := rfl
theorem B_apply (Z : ℝ) (u : D) : B Z u = -dJ u - W u + Z • J u := rfl
theorem C_apply (Z : ℝ) (u : D) : C Z u = dJ u - (2:ℝ) • W u + (Z/2) • J u := rfl

theorem square_A (Z : ℝ) (u : D) :
    ‖A Z u‖^2 = ‖dJ u‖^2 - 2 * Z * coulombMoment u + Z^2 * ‖J u‖^2 :=
  HalfLineSquareAlgebra.square_A (J u) (dJ u) (W u) Z
    (domain_value_gradient_real_zero u) (domain_quotient_gradient_real u)

theorem square_B (Z : ℝ) (u : D) :
    ‖B Z u‖^2 = ‖dJ u‖^2 + 2 * ‖W u‖^2 - 2 * Z * coulombMoment u + Z^2 * ‖J u‖^2 :=
  HalfLineSquareAlgebra.square_B (J u) (dJ u) (W u) Z
    (domain_value_gradient_real_zero u) (domain_quotient_gradient_real u)

theorem square_C (Z : ℝ) (u : D) :
    ‖C Z u‖^2 = ‖dJ u‖^2 + 2 * ‖W u‖^2 - 2 * Z * coulombMoment u + (Z^2/4) * ‖J u‖^2 :=
  HalfLineSquareAlgebra.square_C (J u) (dJ u) (W u) Z
    (domain_value_gradient_real_zero u) (domain_quotient_gradient_real u)

theorem partner_square (Z : ℝ) (u : D) :
    ‖B Z u‖^2 = ‖C Z u‖^2 + (3*Z^2/4) * ‖J u‖^2 :=
  HalfLineSquareAlgebra.square_B_eq_square_C (J u) (dJ u) (W u) Z
    (domain_value_gradient_real_zero u) (domain_quotient_gradient_real u)

theorem derivative_bound_B (Z : ℝ) (u : D) : ‖dJ u‖ ≤ ‖B Z u‖ :=
  HalfLineSquareAlgebra.derivative_norm_le_B (J u) (dJ u) (W u) Z
    (domain_value_gradient_real_zero u) (domain_quotient_gradient_real u)

theorem value_coercivity_B (Z : ℝ) (u : D) :
    (3*Z^2/4) * ‖J u‖^2 ≤ ‖B Z u‖^2 :=
  HalfLineSquareAlgebra.value_coercivity_B (J u) (dJ u) (W u) Z
    (domain_value_gradient_real_zero u) (domain_quotient_gradient_real u)

theorem factor_pairing (Z : ℝ) (u v : D) :
    inner ℂ (A Z u) (J v) = inner ℂ (J u) (B Z v) := by
  rw [A_apply, B_apply]
  simp only [inner_add_left, inner_sub_left, inner_add_right, inner_sub_right,
    inner_neg_right, inner_smul_left_eq_smul, inner_smul_right_eq_smul]
  rw [domain_derivative_pairing, domain_quotient_pairing]

theorem q_square_A (Z : ℝ) (u : D) :
    q Z u = (1/2) * ‖A Z u‖^2 - (Z^2/2) * ‖J u‖^2 := by
  rw [square_A]
  unfold q
  ring

#print axioms square_A
#print axioms square_B
#print axioms square_C
#print axioms partner_square
#print axioms derivative_bound_B
#print axioms value_coercivity_B
#print axioms factor_pairing
#print axioms q_square_A
end TheoremT.HalfLine
