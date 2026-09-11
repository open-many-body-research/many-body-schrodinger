import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic

noncomputable section
open scoped ENNReal
namespace TheoremT.Continuum

theorem young_inverse_difference_nonneg {p r : ℝ} (hp : 0 < p) (hpr : p ≤ r) :
    0 ≤ 1/p-1/r := sub_nonneg.mpr (one_div_le_one_div_of_le hp hpr)

theorem young_three_weights_sum {p q r : ℝ} (h : 1/p+1/q=1+1/r) :
    1/r+(1/p-1/r)+(1/q-1/r)=1 := by linarith

theorem young_product_factorization (x y : ℝ≥0∞) {p q r : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hpr : p ≤ r) (hqr : q ≤ r) :
    (x^p*y^q)^(1/r)*(x^p)^(1/p-1/r)*(y^q)^(1/q-1/r)=x*y := by
  have hb := young_inverse_difference_nonneg hp hpr
  have hc := young_inverse_difference_nonneg hq hqr
  have hx : p*(1/r)+p*(1/p-1/r)=1 := by field_simp; ring
  have hy : q*(1/r)+q*(1/q-1/r)=1 := by field_simp; ring
  calc
    _ = (x^(p*(1/r))*x^(p*(1/p-1/r)))*(y^(q*(1/r))*y^(q*(1/q-1/r))) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
      simp only [← ENNReal.rpow_mul]
      ac_rfl
    _ = x^(p*(1/r)+p*(1/p-1/r))*y^(q*(1/r)+q*(1/q-1/r)) := by
      rw [ENNReal.rpow_add_of_nonneg _ _ (by positivity) (mul_nonneg hp.le hb),
        ENNReal.rpow_add_of_nonneg _ _ (by positivity) (mul_nonneg hq.le hc)]
    _ = _ := by rw [hx,hy,ENNReal.rpow_one,ENNReal.rpow_one]

#print axioms young_product_factorization
end TheoremT.Continuum
