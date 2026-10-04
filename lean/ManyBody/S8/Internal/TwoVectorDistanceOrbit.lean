import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Tactic

/-! Genuine simultaneous physical vector reconstruction from three distances.
Two exact reflections handle collinear, zero and equal vectors without an
orientation, basis, nonzero spectator or independence premise. -/
noncomputable section
open scoped RealInnerProductSpace
namespace ManyBody.S8
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem two_vector_isometry_of_inner (x0 x1 y0 y1 : E)
    (h0 : ‖x0‖ = ‖y0‖) (h1 : ‖x1‖ = ‖y1‖)
    (hinner : inner ℝ x0 x1 = inner ℝ y0 y1) :
    ∃ Q : E ≃ₗᵢ[ℝ] E, Q x0 = y0 ∧ Q x1 = y1 := by
  let R : E ≃ₗᵢ[ℝ] E := (ℝ ∙ (x1-y1))ᗮ.reflection
  have hR1 : R x1 = y1 := Submodule.reflection_sub h1
  have hnorm : ‖R x0‖ = ‖y0‖ := (R.norm_map x0).trans h0
  have hi : inner ℝ (R x0) y1 = inner ℝ y0 y1 := by
    calc
      inner ℝ (R x0) y1 = inner ℝ (R x0) (R x1) := by rw [hR1]
      _ = inner ℝ x0 x1 := R.inner_map_map x0 x1
      _ = inner ℝ y0 y1 := hinner
  let S : E ≃ₗᵢ[ℝ] E := (ℝ ∙ (R x0-y0))ᗮ.reflection
  have hS0 : S (R x0) = y0 := Submodule.reflection_sub hnorm
  have hS1 : S y1 = y1 := by
    apply Submodule.reflection_mem_subspace_eq_self
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left,
      ← real_inner_comm y1 (R x0-y0), inner_sub_left, hi, sub_self]
  exact ⟨R.trans S, hS0, by simpa only [LinearIsometryEquiv.trans_apply, hR1] using hS1⟩

theorem two_vector_isometry_of_distances (x0 x1 y0 y1 : E)
    (h0 : ‖x0‖ = ‖y0‖) (h1 : ‖x1‖ = ‖y1‖)
    (hsep : ‖x0-x1‖ = ‖y0-y1‖) :
    ∃ Q : E ≃ₗᵢ[ℝ] E, Q x0 = y0 ∧ Q x1 = y1 := by
  apply two_vector_isometry_of_inner x0 x1 y0 y1 h0 h1
  have hx := norm_sub_sq_real x0 x1
  have hy := norm_sub_sq_real y0 y1
  rw [h0, h1, hsep] at hx
  linarith

#print axioms two_vector_isometry_of_inner
#print axioms two_vector_isometry_of_distances
end ManyBody.S8
