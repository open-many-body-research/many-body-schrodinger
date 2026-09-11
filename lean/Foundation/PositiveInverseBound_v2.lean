import UnboundedResolvent_v2
import Mathlib.LinearAlgebra.SesquilinearForm.Basic

/-! Elementary coercivity of a nonnegative operator possessing a bounded
inverse. This is an ingredient of the variational/spectral bottom theorem;
no spectral theorem or ground eigenvector is used. -/
noncomputable section
open scoped InnerProductSpace LinearPMap
namespace TheoremT.OperatorTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

local instance : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E

def realOperatorForm (A : E →ₗ.[ℂ] E) : LinearMap.BilinForm ℝ A.domain :=
  (innerₗ E).compl₁₂ (A.domain.subtype.restrictScalars ℝ) (A.toFun.restrictScalars ℝ)

theorem realOperatorForm_apply (A : E →ₗ.[ℂ] E) (x y : A.domain) :
    realOperatorForm A x y = inner ℝ (x : E) (A y) := rfl

theorem positive_inverse_norm_bound (A : E →ₗ.[ℂ] E)
    (hsym : A.IsFormalAdjoint A)
    (hpos : ∀ x : A.domain, 0 ≤ inner ℝ (x : E) (A x))
    (R : E →L[ℂ] E) (hR : ∀ y : E, R y ∈ A.domain)
    (hright : ∀ y : E, A ⟨R y, hR y⟩ = y) (x : A.domain) :
    ‖(x : E)‖ ^ 2 ≤ ‖R‖ * inner ℝ (x : E) (A x) := by
  let y : A.domain := ⟨R (x : E), hR (x : E)⟩
  have hy : A y = (x : E) := hright (x : E)
  have hxy : inner ℝ (y : E) (A x) = ‖(x : E)‖ ^ 2 := by
    have h := congrArg Complex.re (hsym y x)
    change inner ℝ (A y) (x : E) = inner ℝ (y : E) (A x) at h
    rw [hy, real_inner_self_eq_norm_sq] at h
    exact h.symm
  have hcs := (realOperatorForm A).apply_mul_apply_le_of_forall_zero_le hpos x y
  change inner ℝ (x : E) (A y) * inner ℝ (y : E) (A x) ≤
    inner ℝ (x : E) (A x) * inner ℝ (y : E) (A y) at hcs
  rw [hy, hxy, real_inner_self_eq_norm_sq] at hcs
  have hb : inner ℝ (y : E) (x : E) ≤ ‖R‖ * ‖(x : E)‖ ^ 2 := by
    calc
      inner ℝ (y : E) (x : E) ≤ ‖(y : E)‖ * ‖(x : E)‖ := real_inner_le_norm _ _
      _ ≤ (‖R‖ * ‖(x : E)‖) * ‖(x : E)‖ :=
        mul_le_mul_of_nonneg_right (R.le_opNorm (x : E)) (norm_nonneg _)
      _ = ‖R‖ * ‖(x : E)‖ ^ 2 := by ring
  have htotal := hcs.trans (mul_le_mul_of_nonneg_left hb (hpos x))
  by_cases hx : ‖(x : E)‖ = 0
  · rw [hx, zero_pow (by decide : 2 ≠ 0)]
    exact mul_nonneg (norm_nonneg _) (hpos x)
  · have hx2 : 0 < ‖(x : E)‖ ^ 2 := sq_pos_of_ne_zero hx
    nlinarith

theorem positive_inverse_uniform_lower_bound (A : E →ₗ.[ℂ] E)
    (hsym : A.IsFormalAdjoint A)
    (hpos : ∀ x : A.domain, 0 ≤ inner ℝ (x : E) (A x))
    (R : E →L[ℂ] E) (hR : ∀ y : E, R y ∈ A.domain)
    (hright : ∀ y : E, A ⟨R y, hR y⟩ = y) (x : A.domain) :
    (‖R‖ + 1)⁻¹ * ‖(x : E)‖ ^ 2 ≤ inner ℝ (x : E) (A x) := by
  have h := positive_inverse_norm_bound A hsym hpos R hR hright x
  have hr : 0 < ‖R‖ + 1 := by positivity
  apply (inv_mul_le_iff₀ hr).2
  nlinarith [hpos x]

#print axioms positive_inverse_norm_bound
#print axioms positive_inverse_uniform_lower_bound
end TheoremT.OperatorTheory
