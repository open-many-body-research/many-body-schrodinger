import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-! The actual Frechet derivative series divided by factorials. Bounds on
its radius and absolute convergence follow from actual operator norm bounds;
identification of the sum with the function is a separate Taylor theorem. -/
noncomputable section
open scoped BigOperators NNReal ENNReal
namespace TheoremT.Continuum
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def factorialFrechetSeries (f : E → F) (x : E) : FormalMultilinearSeries ℝ E F :=
  fun k => (k.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ k f x

theorem factorialFrechetSeries_apply (f : E → F) (x : E) (k : ℕ) (v : Fin k → E) :
    factorialFrechetSeries f x k v =
      (k.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ k f x v := rfl

theorem factorialFrechetSeries_norm_le (f : E → F) (x : E) {C A : ℝ}
    (hbound : ∀ k, ‖iteratedFDeriv ℝ k f x‖ ≤ C*A^k*(k.factorial : ℝ)) (k : ℕ) :
    ‖factorialFrechetSeries f x k‖ ≤ C*A^k := by
  change ‖(k.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ k f x‖ ≤ _
  rw [norm_smul,Real.norm_of_nonneg (by positivity : 0 ≤ (k.factorial : ℝ)⁻¹)]
  calc
    _ ≤ (k.factorial : ℝ)⁻¹*(C*A^k*(k.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left (hbound k) (by positivity)
    _ = C*A^k := by field_simp

theorem factorialFrechetSeries_radius_ge (f : E → F) (x : E) {C A : ℝ} (r : ℝ≥0)
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hAr : A*(r : ℝ) ≤ 1)
    (hbound : ∀ k, ‖iteratedFDeriv ℝ k f x‖ ≤ C*A^k*(k.factorial : ℝ)) :
    (r : ℝ≥0∞) ≤ (factorialFrechetSeries f x).radius := by
  apply (factorialFrechetSeries f x).le_radius_of_bound C
  intro k
  calc
    ‖factorialFrechetSeries f x k‖*(r : ℝ)^k ≤ (C*A^k)*(r : ℝ)^k :=
      mul_le_mul_of_nonneg_right (factorialFrechetSeries_norm_le f x hbound k) (by positivity)
    _ = C*(A*(r : ℝ))^k := by rw [mul_pow]; ring
    _ ≤ C*1 := mul_le_mul_of_nonneg_left
      (by simpa only [one_pow] using pow_le_pow_left₀ (mul_nonneg hA r.coe_nonneg) hAr k) hC
    _ = C := mul_one C

theorem factorialFrechetSeries_summable_norm (f : E → F) (x y : E) {C A : ℝ}
    (hA : 0 ≤ A) (hq : A*‖y‖ < 1)
    (hbound : ∀ k, ‖iteratedFDeriv ℝ k f x‖ ≤ C*A^k*(k.factorial : ℝ)) :
    Summable (fun k => ‖factorialFrechetSeries f x k (fun _ => y)‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_
    ((summable_geometric_of_lt_one (mul_nonneg hA (norm_nonneg y)) hq).mul_left C)
  intro k
  calc
    _ ≤ ‖factorialFrechetSeries f x k‖*∏ _i : Fin k, ‖y‖ :=
      (factorialFrechetSeries f x k).le_opNorm _
    _ = ‖factorialFrechetSeries f x k‖*‖y‖^k := by simp
    _ ≤ (C*A^k)*‖y‖^k :=
      mul_le_mul_of_nonneg_right (factorialFrechetSeries_norm_le f x hbound k) (by positivity)
    _ = C*(A*‖y‖)^k := by rw [mul_pow]; ring

#print axioms factorialFrechetSeries_radius_ge
#print axioms factorialFrechetSeries_summable_norm
end TheoremT.Continuum
