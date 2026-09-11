import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-! Algebraic consequences of the two compact half-line integration identities.
These generic Hilbert-space identities are conditional; the imported conditions
will be discharged for actual compact half-line functions in a separate module. -/
noncomputable section
open scoped RealInnerProductSpace
namespace TheoremT.HalfLineSquareAlgebra
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem affine_square_identity (u d r : V) (t a b : ℝ)
    (hud : ⟪u,d⟫ = 0) (hrd : 2 * ⟪r,d⟫ = ‖r‖^2) :
    ‖t • d - a • r + b • u‖^2 = t^2 * ‖d‖^2 +
      (a^2 - t*a) * ‖r‖^2 - 2*a*b*⟪r,u⟫ + b^2*‖u‖^2 := by
  have hdu : ⟪d,u⟫ = 0 := by rw [real_inner_comm, hud]
  have hdr : ⟪d,r⟫ = ‖r‖^2 / 2 := by rw [real_inner_comm]; linarith
  rw [norm_add_sq_real, norm_sub_sq_real]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inner_sub_left,
    real_inner_smul_left, real_inner_smul_right, hdu, hdr, mul_zero, sub_zero]
  ring

theorem square_A (u d r : V) (Z : ℝ)
    (hud : ⟪u,d⟫ = 0) (hrd : 2 * ⟪r,d⟫ = ‖r‖^2) :
    ‖d-r+Z•u‖^2 = ‖d‖^2 - 2*Z*⟪r,u⟫ + Z^2*‖u‖^2 := by
  simpa using affine_square_identity u d r 1 1 Z hud hrd

theorem square_B (u d r : V) (Z : ℝ)
    (hud : ⟪u,d⟫ = 0) (hrd : 2 * ⟪r,d⟫ = ‖r‖^2) :
    ‖-d-r+Z•u‖^2 = ‖d‖^2 + 2*‖r‖^2 - 2*Z*⟪r,u⟫ + Z^2*‖u‖^2 := by
  have h := affine_square_identity u d r (-1) 1 Z hud hrd
  norm_num at h
  exact h

theorem square_C (u d r : V) (Z : ℝ)
    (hud : ⟪u,d⟫ = 0) (hrd : 2 * ⟪r,d⟫ = ‖r‖^2) :
    ‖d-(2:ℝ)•r+(Z/2)•u‖^2 = ‖d‖^2 + 2*‖r‖^2 - 2*Z*⟪r,u⟫ +
      (Z^2/4)*‖u‖^2 := by
  have h := affine_square_identity u d r 1 2 (Z/2) hud hrd
  simp only [one_smul] at h
  rw [h]
  ring

theorem square_B_eq_square_C (u d r : V) (Z : ℝ)
    (hud : ⟪u,d⟫ = 0) (hrd : 2 * ⟪r,d⟫ = ‖r‖^2) :
    ‖-d-r+Z•u‖^2 = ‖d-(2:ℝ)•r+(Z/2)•u‖^2 + (3*Z^2/4)*‖u‖^2 := by
  rw [square_B u d r Z hud hrd, square_C u d r Z hud hrd]
  ring

theorem square_B_complete (u d r : V) (Z : ℝ)
    (hud : ⟪u,d⟫ = 0) (hrd : 2 * ⟪r,d⟫ = ‖r‖^2) :
    ‖-d-r+Z•u‖^2 = ‖d‖^2 + 2 * ‖r-(Z/2)•u‖^2 + (Z^2/2)*‖u‖^2 := by
  rw [square_B u d r Z hud hrd, norm_sub_sq_real]
  simp only [real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

theorem derivative_norm_le_B (u d r : V) (Z : ℝ)
    (hud : ⟪u,d⟫ = 0) (hrd : 2 * ⟪r,d⟫ = ‖r‖^2) :
    ‖d‖ ≤ ‖-d-r+Z•u‖ := by
  have h := square_B_complete u d r Z hud hrd
  have hh : 0 ≤ (Z^2/2)*‖u‖^2 := by positivity
  nlinarith [norm_nonneg d, norm_nonneg (-d-r+Z•u), sq_nonneg ‖r-(Z/2)•u‖]

theorem value_coercivity_B (u d r : V) (Z : ℝ)
    (hud : ⟪u,d⟫ = 0) (hrd : 2 * ⟪r,d⟫ = ‖r‖^2) :
    (3*Z^2/4)*‖u‖^2 ≤ ‖-d-r+Z•u‖^2 := by
  rw [square_B_eq_square_C u d r Z hud hrd]
  exact le_add_of_nonneg_left (sq_nonneg _)

#print axioms affine_square_identity
#print axioms derivative_norm_le_B
#print axioms value_coercivity_B
end TheoremT.HalfLineSquareAlgebra
