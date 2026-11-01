import GrushinScalarFixedGapRecurrence_v1
import GrushinFactorialAmplitudeMajorant_v1
import GrushinRecurrenceCoefficientAbsorption_v1

/-! R18 implies the precise R23 scalar bound, under the stated monotonicity
and base estimates. The proof only rescales by h^r, never divides by F+H0.
This remains conditional on the actual unnormalized fixed-gap recurrence;
no weighted PDE recurrence is proved by this scalar module. -/
noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum

theorem grushin_scalar_fixed_gap_grid_bound (N : ℕ → ℝ → ℝ)
    {ρ C A F H0 : ℝ} {ell r : ℕ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hC : 1 ≤ C) (hA : 1 ≤ A)
    (hF : 0 ≤ F) (hH0 : 0 ≤ H0) (hr : r < ell)
    (hN : ∀ q s, 0 ≤ s → s ≤ ρ → 0 ≤ N q s)
    (hmono : ∀ q s t, 0 ≤ s → s ≤ t → t ≤ ρ → N q t ≤ N q s)
    (hbase : ∀ q, q ≤ 8 → ∀ s, 0 ≤ s → s ≤ ρ → N q s ≤ H0)
    (hrec : GrushinScalarFixedGapRecurrence N ρ C A F) :
    grushinGridNorm N (ρ/(ell : ℝ)) r ≤ (F+H0)*(2*(2*C*A))^(r+1) := by
  let d := grushinGridNorm N (ρ/(ell : ℝ))
  have hS : 0 ≤ F+H0 := add_nonneg hF hH0
  have hB : 1 ≤ 2*C*A := by
    have hCA := one_le_mul_of_one_le_of_one_le hC hA
    nlinarith
  apply factorial_majorant_amplitude_bound (2*C*A) (F+H0) hB hS 9 ell d ?_ ?_ r hr
  · intro q hq hq9
    exact (grushin_gridNorm_base N hρ hρ1 hq hH0 (hbase q (by omega))).trans
      (le_add_of_nonneg_left hF)
  · intro q hq hq9
    have hn := grushin_grid_recurrence_from_fixed_gap N hρ hρ1
      (zero_le_one.trans hC) (zero_le_one.trans hA) hF
      (le_add_of_nonneg_right hH0) hq hq9 hN hmono hrec
    have hd : ∀ k ≤ q, 0 ≤ d k := by
      intro k hk
      exact grushin_gridNorm_nonneg N hρ (by omega) hN
    exact hn.trans (grushin_recurrence_coefficient_absorption C A (F+H0) q d
      hC hA hS (by omega) hd)

theorem grushin_scalar_fixed_gap_bound (N : ℕ → ℝ → ℝ)
    {ρ C A F H0 : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hC : 1 ≤ C) (hA : 1 ≤ A)
    (hF : 0 ≤ F) (hH0 : 0 ≤ H0)
    (hN : ∀ q s, 0 ≤ s → s ≤ ρ → 0 ≤ N q s)
    (hmono : ∀ q s t, 0 ≤ s → s ≤ t → t ≤ ρ → N q t ≤ N q s)
    (hbase : ∀ q, q ≤ 8 → ∀ s, 0 ≤ s → s ≤ ρ → N q s ≤ H0)
    (hrec : GrushinScalarFixedGapRecurrence N ρ C A F) (r : ℕ) :
    let B := 2*C*A
    let S := F+H0
    N r ρ ≤ 2*B*S*(2*B*((r : ℝ)+1)/ρ)^r := by
  let h := ρ/((r+1 : ℕ) : ℝ)
  let B := 2*C*A
  let S := F+H0
  have hh : 0 < h := grushin_normalization_scale_pos hρ (by omega)
  have htime : ((r : ℝ)+1)*h = ρ := by
    dsimp [h]
    push_cast
    field_simp
  have hb := grushin_scalar_fixed_gap_grid_bound N hρ hρ1 hC hA hF hH0
    (ell := r+1) (r := r) (by omega) hN hmono hbase hrec
  have hs : h^r*N r ρ ≤ S*(2*B)^(r+1) := by
    change h^r*N r (((r : ℝ)+1)*h) ≤ S*(2*B)^(r+1) at hb
    simpa only [htime] using hb
  change N r ρ ≤ 2*B*S*(2*B*((r : ℝ)+1)/ρ)^r
  calc
    N r ρ ≤ (S*(2*B)^(r+1))/h^r :=
      (le_div_iff₀ (pow_pos hh r)).2 (by simpa only [mul_comm] using hs)
    _ = (2*B)*S*((2*B)/h)^r := by rw [div_pow,pow_succ]; ring
    _ = 2*B*S*(2*B*((r : ℝ)+1)/ρ)^r := by
      simp only [h,Nat.cast_add,Nat.cast_one,div_div_eq_mul_div]

theorem grushin_scalar_fixed_gap_zero (N : ℕ → ℝ → ℝ)
    {ρ C A F H0 : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hC : 1 ≤ C) (hA : 1 ≤ A)
    (hF : 0 ≤ F) (hH0 : 0 ≤ H0) (hS : F+H0 = 0)
    (hN : ∀ q s, 0 ≤ s → s ≤ ρ → 0 ≤ N q s)
    (hmono : ∀ q s t, 0 ≤ s → s ≤ t → t ≤ ρ → N q t ≤ N q s)
    (hbase : ∀ q, q ≤ 8 → ∀ s, 0 ≤ s → s ≤ ρ → N q s ≤ H0)
    (hrec : GrushinScalarFixedGapRecurrence N ρ C A F) (r : ℕ) : N r ρ = 0 := by
  apply le_antisymm
  · have h := grushin_scalar_fixed_gap_bound N hρ hρ1 hC hA hF hH0 hN hmono hbase hrec r
    simpa only [hS,mul_zero,zero_mul] using h
  · exact hN r ρ hρ.le le_rfl

#print axioms grushin_scalar_fixed_gap_bound
#print axioms grushin_scalar_fixed_gap_zero
end TheoremT.Continuum
