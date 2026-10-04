import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic

/-! Actual unit complex phases separate distinct natural powers.
For exponents m,n the explicit phase exp(2*pi*I/(m+n+1)) has order
m+n+1. Both exponents lie strictly below this order, so equality of
their powers forces equality of exponents. No invariant-support claim
is assumed in this separation lemma. -/
set_option autoImplicit false
namespace TheoremT.Continuum

theorem complex_exists_unit_phase_pow_ne {m n : ℕ} (hne : m ≠ n) :
    ∃ u : ℂ, ‖u‖ = 1 ∧ u^m ≠ u^n := by
  have hN : m+n+1 ≠ 0 := by omega
  have hroot := Complex.isPrimitiveRoot_exp (m+n+1) hN
  refine ⟨Complex.exp (2 * Real.pi * Complex.I / (m+n+1 : ℕ)),
    hroot.norm'_eq_one hN, ?_⟩
  intro heq
  exact hne (hroot.pow_inj (by omega) (by omega) heq)

theorem complex_nat_eq_of_unit_phase_pow_eq {m n : ℕ}
    (h : ∀ u : ℂ, ‖u‖ = 1 → u^m = u^n) : m = n := by
  by_contra hne
  obtain ⟨u, hu, hpow⟩ := complex_exists_unit_phase_pow_ne hne
  exact hpow (h u hu)

end TheoremT.Continuum
