import Mathlib.Analysis.InnerProductSpace.Symmetric

/-! The projection algebra in the two-electron hydrogenic comparison.
Actual one-electron projection maps, their commutation and component form
bounds must still be constructed on the physical space. This file proves
the norm inequality and its exact kinetic-normalization constants. -/
noncomputable section
namespace TheoremT.OperatorTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem symmetric_projection_norm_decomposition
    (P : E →ₗ[ℂ] E) (hP : P.IsSymmetricProjection) (x : E) :
    ‖x‖^2 = ‖P x‖^2 + ‖x-P x‖^2 := by
  have hid : P (P x) = P x := by
    have hh := congrArg (fun T : E →ₗ[ℂ] E => T x) hP.isIdempotentElem
    simpa only [Module.End.mul_apply] using hh
  have hi : (inner ℂ x (P x)).re = ‖P x‖^2 := by
    have hh := hP.isSymmetric x (P x)
    rw [hid,inner_self_eq_norm_sq_to_K] at hh
    have hr := congrArg Complex.re hh
    simpa [← Complex.ofReal_pow] using hr.symm
  change RCLike.re (inner ℂ x (P x)) = ‖P x‖^2 at hi
  rw [norm_sub_sq (𝕜 := ℂ),hi]
  ring

theorem symmetric_projection_norm_square_le
    (P : E →ₗ[ℂ] E) (hP : P.IsSymmetricProjection) (x : E) :
    ‖P x‖^2 ≤ ‖x‖^2 := by
  have h := symmetric_projection_norm_decomposition P hP x
  nlinarith [sq_nonneg ‖x-P x‖]

theorem commuting_projections_norm_square
    (P Q : E →ₗ[ℂ] E) (hP : P.IsSymmetricProjection) (hQ : Q.IsSymmetricProjection)
    (hcomm : Commute P Q) (x : E) :
    ‖P x‖^2 + ‖Q x‖^2 ≤ ‖x‖^2 + ‖P (Q x)‖^2 := by
  have hcomx : Q (P x) = P (Q x) := by
    have hh := congrArg (fun T : E →ₗ[ℂ] E => T x) hcomm.eq
    simpa only [Module.End.mul_apply] using hh.symm
  have h1 := symmetric_projection_norm_decomposition P hP x
  have h2 := symmetric_projection_norm_decomposition P hP (Q x)
  have h3 := symmetric_projection_norm_square_le Q hQ (x-P x)
  rw [map_sub,hcomx] at h3
  linarith

theorem two_hydrogenic_comparisons_combine
    (P Q : E →ₗ[ℂ] E) (hP : P.IsSymmetricProjection) (hQ : Q.IsSymmetricProjection)
    (hcomm : Commute P Q) (x : E) (Z e1 e2 e : ℝ)
    (h1 : -(Z^2/8) * ‖x‖^2 - (3*Z^2/8) * ‖P x‖^2 ≤ e1)
    (h2 : -(Z^2/8) * ‖x‖^2 - (3*Z^2/8) * ‖Q x‖^2 ≤ e2)
    (he : e1+e2 ≤ e) :
    -(5*Z^2/8) * ‖x‖^2 ≤ e + (3*Z^2/8) * ‖P (Q x)‖^2 := by
  have hp := commuting_projections_norm_square P Q hP hQ hcomm x
  have hm := mul_le_mul_of_nonneg_left hp (sq_nonneg Z)
  nlinarith

#print axioms symmetric_projection_norm_decomposition
#print axioms symmetric_projection_norm_square_le
#print axioms commuting_projections_norm_square
#print axioms two_hydrogenic_comparisons_combine
end TheoremT.OperatorTheory
