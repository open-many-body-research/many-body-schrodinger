import MultiindexCoordinateWord_v1
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Tactic

/-! The chosen multiindex word has the actual prescribed number of
occurrences of each coordinate. Apply its proved real product identity
to weight two at the chosen coordinate and one elsewhere, then use
injectivity of the natural powers of two. No occurrence count is assumed. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem multiindexCoordinateWord_count (α : ι → ℕ) (i : ι) :
    (Finset.univ.filter (fun j => multiindexCoordinateWord α j = i)).card = α i := by
  have hprod := multiindexCoordinateWord_prod α (fun k => if k = i then (2 : ℝ) else 1)
  have hleft : (∏ j, if multiindexCoordinateWord α j = i then (2 : ℝ) else 1) =
      (2 : ℝ) ^ (Finset.univ.filter (fun j => multiindexCoordinateWord α j = i)).card := by
    rw [Finset.prod_ite]
    simp
  have hright : (∏ k, (if k = i then (2 : ℝ) else 1) ^ α k) = (2 : ℝ) ^ α i := by
    simp only [ite_pow, one_pow]
    simp
  apply pow_right_injective₀ (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)
  exact hleft.symm.trans (hprod.trans hright)

end TheoremT.Continuum
