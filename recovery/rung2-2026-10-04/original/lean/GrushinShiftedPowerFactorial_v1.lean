import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-! The exact elementary numeric inequality used in R25. A nonnegative
term of the exponential series bounds the shifted core power directly, so
the proof includes k=0 without division by k or an asymptotic estimate. -/
noncomputable section
namespace TheoremT.Continuum

theorem grushin_successor_le_two_pow (k : ℕ) : (k : ℝ)+1 ≤ (2 : ℝ)^k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    simp only [Nat.cast_add_one, pow_succ]
    nlinarith [Nat.cast_nonneg (α := ℝ) k]

theorem grushin_shifted_core_power_factorial_bound (k : ℕ) :
    ((k : ℝ)+12)^k ≤ (3 : ℝ)^(k+12)*(k.factorial : ℝ) := by
  have hfac : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hcore : ((k : ℝ)+12)^k ≤ Real.exp ((k : ℝ)+12)*(k.factorial : ℝ) :=
    (div_le_iff₀ hfac).1 (Real.pow_div_factorial_le_exp ((k : ℝ)+12) (by positivity) k)
  have he : Real.exp ((k : ℝ)+12) ≤ (3 : ℝ)^(k+12) := by
    calc
      _ = Real.exp 1 ^ (k+12) := by
        simpa only [Nat.cast_add, Nat.cast_ofNat, mul_one] using Real.exp_nat_mul 1 (k+12)
      _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le (k+12)
  exact hcore.trans (mul_le_mul_of_nonneg_right he hfac.le)

theorem grushin_shifted_power_factorial_bound (k : ℕ) :
    ((k : ℝ)+12)^(k+11) ≤
      (3 : ℝ)^12*(12 : ℝ)^11*(6144 : ℝ)^k*(k.factorial : ℝ) := by
  have hbase : (k : ℝ)+12 ≤ 12*(2 : ℝ)^k := by
    nlinarith [grushin_successor_le_two_pow k, Nat.cast_nonneg (α := ℝ) k]
  have hpoly : ((k : ℝ)+12)^11 ≤ (12*(2 : ℝ)^k)^11 :=
    pow_le_pow_left₀ (by positivity) hbase 11
  have h2 : ((2 : ℝ)^k)^11 = (2048 : ℝ)^k := by
    calc
      _ = ((2 : ℝ)^11)^k := by rw [← pow_mul, ← pow_mul, Nat.mul_comm k 11]
      _ = _ := by norm_num
  have h6144 : (6144 : ℝ)^k = (3 : ℝ)^k*(2048 : ℝ)^k := by
    rw [← mul_pow]
    norm_num
  calc
    _ = ((k : ℝ)+12)^k * ((k : ℝ)+12)^11 := pow_add _ k 11
    _ ≤ ((3 : ℝ)^(k+12)*(k.factorial : ℝ)) * (12*(2 : ℝ)^k)^11 :=
      mul_le_mul (grushin_shifted_core_power_factorial_bound k) hpoly
        (by positivity) (by positivity)
    _ = _ := by
      rw [pow_add, mul_pow, h2, h6144]
      ring

end TheoremT.Continuum
