import Mathlib.Tactic

/-! Scalar coefficient absorption for the normalized Grushin recurrence.
The two preceding terms are included in the first two geometric sum terms.
No recurrence bound, PDE estimate, or derivative identification is assumed. -/
noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum

theorem grushin_first_two_le_geometric_sum (A : ℝ) (r : ℕ) (d : ℕ → ℝ)
    (hA : 1 ≤ A) (hr : 2 ≤ r) (hd : ∀ q ≤ r, 0 ≤ d q) :
    d (r-1) + d (r-2) ≤ ∑ j ∈ Finset.range r, A^(j+1) * d (r-1-j) := by
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hA2 : 1 ≤ A^2 := by
    simpa only [one_pow] using pow_le_pow_left₀ zero_le_one hA 2
  have hfirst : d (r-1) ≤ A * d (r-1) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hA (hd _ (by omega))
  have hsecond : d (r-2) ≤ A^2 * d (r-2) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hA2 (hd _ (by omega))
  have hsum : (∑ j ∈ Finset.range 2, A^(j+1) * d (r-1-j)) ≤
      ∑ j ∈ Finset.range r, A^(j+1) * d (r-1-j) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hr)
    intro j _ _
    exact mul_nonneg (pow_nonneg hA0 _) (hd _ (by omega))
  have htwo : (∑ j ∈ Finset.range 2, A^(j+1) * d (r-1-j)) =
      A * d (r-1) + A^2 * d (r-2) := by
    norm_num [Finset.sum_range_succ, Nat.sub_sub]
  exact (add_le_add hfirst hsecond).trans (htwo ▸ hsum)

theorem grushin_recurrence_power_coefficient_le (C A : ℝ)
    (hC : 1 ≤ C) (hA : 0 ≤ A) (j : ℕ) :
    (2*C) * A^(j+1) ≤ (2*C*A)^(j+1) := by
  have h2C : 1 ≤ 2*C := by linarith
  have hp : 2*C ≤ (2*C)^(j+1) := le_self_pow₀ h2C (Nat.succ_ne_zero j)
  calc
    _ ≤ (2*C)^(j+1) * A^(j+1) :=
      mul_le_mul_of_nonneg_right hp (pow_nonneg hA _)
    _ = (2*C*A)^(j+1) := (mul_pow (2*C) A (j+1)).symm

theorem grushin_recurrence_coefficient_absorption (C A S : ℝ) (r : ℕ) (d : ℕ → ℝ)
    (hC : 1 ≤ C) (hA : 1 ≤ A) (hS : 0 ≤ S) (hr : 2 ≤ r)
    (hd : ∀ q ≤ r, 0 ≤ d q) :
    C * (S*A^r + d (r-1) + d (r-2) +
      ∑ j ∈ Finset.range r, A^(j+1) * d (r-1-j)) ≤
      S*(2*C*A)^(r+1) + ∑ j ∈ Finset.range r, (2*C*A)^(j+1) * d (r-1-j) := by
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hB0 : 0 ≤ 2*C*A := by positivity
  have h2C : 1 ≤ 2*C := by linarith
  have hAB : A ≤ 2*C*A := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right h2C hA0
  have hCB : C ≤ 2*C*A := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hA) hC0]
  have hp : C * A^r ≤ (2*C*A)^(r+1) := by
    have hh := mul_le_mul hCB (pow_le_pow_left₀ hA0 hAB r) (pow_nonneg hA0 r) hB0
    simpa only [pow_succ'] using hh
  have hsource : C * (S*A^r) ≤ S*(2*C*A)^(r+1) := by
    calc
      _ = S*(C*A^r) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hp hS
  have hfirst := grushin_first_two_le_geometric_sum A r d hA hr hd
  have hdouble : C * (d (r-1) + d (r-2) +
      ∑ j ∈ Finset.range r, A^(j+1) * d (r-1-j)) ≤
      (2*C) * (∑ j ∈ Finset.range r, A^(j+1) * d (r-1-j)) := by
    calc
      _ ≤ C * ((∑ j ∈ Finset.range r, A^(j+1) * d (r-1-j)) +
          ∑ j ∈ Finset.range r, A^(j+1) * d (r-1-j)) :=
        mul_le_mul_of_nonneg_left (add_le_add hfirst le_rfl) hC0
      _ = _ := by ring
  have hsum : (2*C) * (∑ j ∈ Finset.range r, A^(j+1) * d (r-1-j)) ≤
      ∑ j ∈ Finset.range r, (2*C*A)^(j+1) * d (r-1-j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
      (grushin_recurrence_power_coefficient_le C A hC hA0 j) (hd _ (by omega))
  calc
    _ = C*(S*A^r) + C*(d (r-1) + d (r-2) +
        ∑ j ∈ Finset.range r, A^(j+1) * d (r-1-j)) := by ring
    _ ≤ S*(2*C*A)^(r+1) + (2*C) *
        (∑ j ∈ Finset.range r, A^(j+1) * d (r-1-j)) := add_le_add hsource hdouble
    _ ≤ _ := add_le_add le_rfl hsum

end TheoremT.Continuum
