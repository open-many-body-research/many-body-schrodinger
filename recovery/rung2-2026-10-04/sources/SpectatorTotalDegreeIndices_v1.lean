import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-! Finite index sets for grouping one radial homogeneous degree together
with all spectator exponents. The zero coordinate is the radial degree;
the remaining d coordinates are the actual spectator multiindex. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum

def spectatorTotalDegreeIndices (d n : ℕ) : Finset (Fin (d+1) →₀ ℕ) :=
  Finset.finsuppAntidiag Finset.univ n

theorem mem_spectatorTotalDegreeIndices_iff (d n : ℕ) (w : Fin (d+1) →₀ ℕ) :
    w ∈ spectatorTotalDegreeIndices d n ↔ w 0 + ∑ i : Fin d, w i.succ = n := by
  simp only [spectatorTotalDegreeIndices,Finset.mem_finsuppAntidiag,
    Finset.subset_univ,and_true,Fin.sum_univ_succ]

theorem card_spectatorTotalDegreeIndices (d n : ℕ) :
    (spectatorTotalDegreeIndices d n).card = (n+d).choose d := by
  rw [spectatorTotalDegreeIndices,Finset.card_finsuppAntidiag_nat_eq_choose]
  simp only [Finset.card_univ,Fintype.card_fin]
  have h : d+1+n-1 = n+d := by omega
  rw [h,Nat.choose_symm_add]

end TheoremT.Continuum
