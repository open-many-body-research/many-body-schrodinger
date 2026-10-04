import MonomialExponentWord_v1
import Mathlib.Data.Real.Basic

/-! A fixed coordinate word for an actual finite multiindex, with the
exact monomial product identity for every real weight. The exponent
function is converted to its actual Finsupp; zero exponents are restored
when the support product is rewritten as a full finite-coordinate product.
The representative is selected with Classical.choose. It has no advertised
intrinsic ordering and is not an executable word-generation algorithm. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum
variable {ι : Type*} [Fintype ι]

theorem multiindex_coordinate_word_exists (α : ι → ℕ) :
    ∃ w : Fin (∑ i, α i) → ι, ∀ weight : ι → ℝ,
      (∏ j, weight (w j)) = ∏ i, weight i ^ α i := by
  classical
  let e : ι →₀ ℕ := Finsupp.equivFunOnFinite.symm α
  have he : e.sum (fun _ n => n) = ∑ i, α i := by
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    simp [e]
  obtain ⟨w, hw⟩ := monomial_exponent_word_exists (M := ℝ) e (∑ i, α i) he
  refine ⟨w, fun weight => ?_⟩
  rw [hw]
  change e.prod (fun i n => weight i ^ n) = _
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp [e]

def multiindexCoordinateWord (α : ι → ℕ) : Fin (∑ i, α i) → ι :=
  (multiindex_coordinate_word_exists α).choose

theorem multiindexCoordinateWord_prod (α : ι → ℕ) (weight : ι → ℝ) :
    (∏ j, weight (multiindexCoordinateWord α j)) = ∏ i, weight i ^ α i :=
  (multiindex_coordinate_word_exists α).choose_spec weight

end TheoremT.Continuum
