import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-! The shift-one exponential-series estimate and its exact application
to the R23 profile majorant. All natural orders, including zero, are
handled directly; neither the order nor the data norm is divided out. -/
noncomputable section
namespace TheoremT.Continuum

theorem grushin_successor_core_power_factorial_bound (r : ℕ) :
    ((r : ℝ)+1)^r ≤ (3 : ℝ)^(r+1)*(r.factorial : ℝ) := by
  have hfac : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
  have hcore : ((r : ℝ)+1)^r ≤ Real.exp ((r : ℝ)+1)*(r.factorial : ℝ) :=
    (div_le_iff₀ hfac).1 (Real.pow_div_factorial_le_exp ((r : ℝ)+1) (by positivity) r)
  have he : Real.exp ((r : ℝ)+1) ≤ (3 : ℝ)^(r+1) := by
    calc
      _ = Real.exp 1 ^ (r+1) := by
        simpa only [Nat.cast_add, Nat.cast_one, mul_one] using Real.exp_nat_mul 1 (r+1)
      _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le (r+1)
  exact hcore.trans (mul_le_mul_of_nonneg_right he hfac.le)

theorem grushin_r23_factorial_bound (r : ℕ) {ρ B S N : ℝ}
    (hρ : 0 < ρ) (hB : 0 ≤ B) (hS : 0 ≤ S)
    (hN : N ≤ 2*B*S*(2*B*((r : ℝ)+1)/ρ)^r) :
    N ≤ 6*B*S*(6*B/ρ)^r*(r.factorial : ℝ) := by
  have hsplit : (2*B*((r : ℝ)+1)/ρ)^r = (2*B/ρ)^r*((r : ℝ)+1)^r := by
    rw [← mul_pow]
    congr 1
    ring
  have hscale : (6*B/ρ)^r = (3 : ℝ)^r*(2*B/ρ)^r := by
    rw [← mul_pow]
    congr 1
    ring
  calc
    N ≤ 2*B*S*(2*B*((r : ℝ)+1)/ρ)^r := hN
    _ = (2*B*S*(2*B/ρ)^r)*((r : ℝ)+1)^r := by rw [hsplit]; ring
    _ ≤ (2*B*S*(2*B/ρ)^r)*((3 : ℝ)^(r+1)*(r.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left (grushin_successor_core_power_factorial_bound r) (by positivity)
    _ = 6*B*S*(6*B/ρ)^r*(r.factorial : ℝ) := by
      rw [hscale, pow_succ]
      ring

end TheoremT.Continuum
