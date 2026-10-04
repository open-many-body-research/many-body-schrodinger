import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic

/-!
Finite trace bounds in any normed additive commutative group, hence in actual
L2 spaces. The constants display the finite index cardinalities explicitly.
No linear independence, orthogonality, nonempty index type, or analytic
regularity is assumed. These estimates control a sum of vectors by the sum
of their squared norms; they do not assert existence of any derivative.
-/
open scoped BigOperators

namespace TheoremT.Continuum

variable {E I J : Type*} [NormedAddCommGroup E] [Fintype I] [Fintype J]

theorem finite_sum_norm_sq_le_card_sum_norm_sq (u : I → E) :
    ‖∑ i : I, u i‖ ^ 2 ≤ (Fintype.card I : ℝ) * ∑ i : I, ‖u i‖ ^ 2 := by
  have hnorm := norm_sum_le Finset.univ u
  have hsquare := pow_le_pow_left₀ (norm_nonneg (∑ i : I, u i)) hnorm 2
  exact hsquare.trans (by simpa only [Finset.card_univ] using
    (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : I => ‖u i‖)))

theorem trace_norm_add_sq_le_weighted (a b : E) {τ : ℝ} (hτ : 0 < τ) :
    ‖a + b‖ ^ 2 ≤ (1 + τ) * ‖a‖ ^ 2 + (1 + 1 / τ) * ‖b‖ ^ 2 := by
  have hnorm := pow_le_pow_left₀ (norm_nonneg (a + b)) (norm_add_le a b) 2
  have hid : (1 + τ) * ‖a‖ ^ 2 + (1 + 1 / τ) * ‖b‖ ^ 2 -
      (‖a‖ + ‖b‖) ^ 2 = (τ * ‖a‖ - ‖b‖) ^ 2 / τ := by
    field_simp
    ring
  have hnonneg := div_nonneg (sq_nonneg (τ * ‖a‖ - ‖b‖)) hτ.le
  linarith

theorem grouped_sum_norm_sq_le_weighted_card_sums
    (u : I → E) (v : J → E) {τ : ℝ} (hτ : 0 < τ) :
    ‖(∑ i : I, u i) + ∑ j : J, v j‖ ^ 2 ≤
      (1 + τ) * (Fintype.card I : ℝ) * (∑ i : I, ‖u i‖ ^ 2) +
      (1 + 1 / τ) * (Fintype.card J : ℝ) * (∑ j : J, ‖v j‖ ^ 2) := by
  have hsum := trace_norm_add_sq_le_weighted (∑ i : I, u i) (∑ j : J, v j) hτ
  have hu := mul_le_mul_of_nonneg_left (finite_sum_norm_sq_le_card_sum_norm_sq u)
    (by positivity : 0 ≤ 1 + τ)
  have hv := mul_le_mul_of_nonneg_left (finite_sum_norm_sq_le_card_sum_norm_sq v)
    (by positivity : 0 ≤ 1 + 1 / τ)
  nlinarith

theorem grouped_sum_norm_sq_le_card_sums (u : I → E) (v : J → E) :
    ‖(∑ i : I, u i) + ∑ j : J, v j‖ ^ 2 ≤
      2 * (Fintype.card I : ℝ) * (∑ i : I, ‖u i‖ ^ 2) +
      2 * (Fintype.card J : ℝ) * (∑ j : J, ‖v j‖ ^ 2) := by
  have h := grouped_sum_norm_sq_le_weighted_card_sums u v (by norm_num : (0 : ℝ) < 1)
  norm_num at h
  exact h

#print axioms finite_sum_norm_sq_le_card_sum_norm_sq
#print axioms trace_norm_add_sq_le_weighted
#print axioms grouped_sum_norm_sq_le_weighted_card_sums
#print axioms grouped_sum_norm_sq_le_card_sums

end TheoremT.Continuum
