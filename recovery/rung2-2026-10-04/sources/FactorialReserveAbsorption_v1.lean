import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic

/-! Absorbing a fixed derivative reserve into an explicit analytic bound.
The constants are derived from the binomial theorem and retain the exact
dependence on the reserve and on the original exponential base. -/
noncomputable section
set_option autoImplicit false
namespace TheoremT.Continuum.WeakGrushin

theorem factorial_add_le_two_pow (k r : ℕ) :
    ((k+r).factorial : ℝ) ≤ (2 : ℝ)^(k+r)*(k.factorial : ℝ)*(r.factorial : ℝ) := by
  have h : (k+r).factorial ≤ 2^(k+r)*k.factorial*r.factorial := by
    rw [← Nat.add_choose_mul_factorial_mul_factorial]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.choose_le_two_pow (k+r) r))
  exact_mod_cast h

theorem factorial_reserve_absorption {D B : ℝ} (hD : 0 ≤ D) (hB : 0 ≤ B)
    (k r : ℕ) :
    D*B^(k+r)*((k+r).factorial : ℝ) ≤
      (D*(2*B)^r*(r.factorial : ℝ))*(2*B)^k*(k.factorial : ℝ) := by
  calc
    _ ≤ D*B^(k+r)*((2 : ℝ)^(k+r)*(k.factorial : ℝ)*(r.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left (factorial_add_le_two_pow k r) (by positivity)
    _ = _ := by rw [pow_add,pow_add,mul_pow,mul_pow]; ring

end TheoremT.Continuum.WeakGrushin
