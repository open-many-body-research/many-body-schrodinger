import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic

/-! An explicit dimension loss when total-order factorial bounds are
converted into coordinate multiindex factorial bounds. The multinomial
comparison follows from the actual finite multinomial expansion at all
coordinate values one. Empty coordinates and total degree zero are
included. This is a prerequisite for a corrected derivative-rate route,
not a proof of the exact original D6 Cauchy bound. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum
variable {ι : Type*} [Fintype ι]

theorem multinomial_univ_le_card_pow_sum (α : ι → ℕ) :
    Nat.multinomial Finset.univ α ≤ (Fintype.card ι) ^ (∑ i, α i) := by
  classical
  have hexpand : (Fintype.card ι) ^ (∑ i, α i) =
      ∑ k ∈ Finset.piAntidiag (Finset.univ : Finset ι) (∑ i, α i),
        Nat.multinomial Finset.univ k := by
    simpa using Finset.sum_pow_eq_sum_piAntidiag
      (Finset.univ : Finset ι) (fun _ : ι => (1 : ℕ)) (∑ i, α i)
  have hmem : α ∈ Finset.piAntidiag (Finset.univ : Finset ι) (∑ i, α i) := by
    simp [Finset.mem_piAntidiag]
  calc
    _ ≤ ∑ k ∈ Finset.piAntidiag (Finset.univ : Finset ι) (∑ i, α i),
        Nat.multinomial Finset.univ k :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem
    _ = _ := hexpand.symm

theorem factorial_sum_le_card_pow_mul_prod_factorial (α : ι → ℕ) :
    (∑ i, α i).factorial ≤
      (Fintype.card ι) ^ (∑ i, α i) * ∏ i, (α i).factorial := by
  calc
    _ = (∏ i, (α i).factorial) * Nat.multinomial Finset.univ α :=
      (Nat.multinomial_spec Finset.univ α).symm
    _ ≤ (∏ i, (α i).factorial) * (Fintype.card ι) ^ (∑ i, α i) :=
      Nat.mul_le_mul_left _ (multinomial_univ_le_card_pow_sum α)
    _ = _ := Nat.mul_comm _ _

theorem factorial_sum_le_card_pow_mul_prod_factorial_real (α : ι → ℕ) :
    ((∑ i, α i).factorial : ℝ) ≤
      (Fintype.card ι : ℝ) ^ (∑ i, α i) * ∏ i, ((α i).factorial : ℝ) := by
  exact_mod_cast factorial_sum_le_card_pow_mul_prod_factorial α

end TheoremT.Continuum
