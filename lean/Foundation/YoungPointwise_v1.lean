import HolderThreeWeights_v1
import YoungWeights_v1

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace TheoremT.Continuum

theorem young_pointwise_lintegral_le {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g : X → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    {p q r : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hpr : p ≤ r) (hqr : q ≤ r) (hs : 1/p+1/q=1+1/r) :
    (∫⁻ x, f x*g x ∂μ) ≤
      (∫⁻ x, f x^p*g x^q ∂μ)^(1/r) *
        (∫⁻ x, f x^p ∂μ)^(1/p-1/r) * (∫⁻ x, g x^q ∂μ)^(1/q-1/r) := by
  have ht := lintegral_three_weighted_le ((hf.pow_const p).mul (hg.pow_const q))
    (hf.pow_const p) (hg.pow_const q) (a := 1/r) (b := 1/p-1/r) (c := 1/q-1/r)
    (by positivity) (young_inverse_difference_nonneg hp hpr)
    (young_inverse_difference_nonneg hq hqr) (young_three_weights_sum hs)
  simpa only [Pi.mul_apply, young_product_factorization _ _ hp hq hr hpr hqr] using ht

theorem young_pointwise_power_le {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g : X → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    {p q r : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hpr : p ≤ r) (hqr : q ≤ r) (hs : 1/p+1/q=1+1/r) :
    (∫⁻ x, f x*g x ∂μ)^r ≤
      (∫⁻ x, f x^p*g x^q ∂μ) *
        (∫⁻ x, f x^p ∂μ)^(r/p-1) * (∫⁻ x, g x^q ∂μ)^(r/q-1) := by
  have ht := ENNReal.rpow_le_rpow (young_pointwise_lintegral_le hf hg hp hq hr hpr hqr hs) hr.le
  have ha : (1/r)*r=1 := by field_simp
  have hb : (1/p-1/r)*r=r/p-1 := by field_simp
  have hc : (1/q-1/r)*r=r/q-1 := by field_simp
  simpa only [ENNReal.mul_rpow_of_nonneg _ _ hr.le, ← ENNReal.rpow_mul,
    ha, hb, hc, ENNReal.rpow_one] using ht

#print axioms young_pointwise_power_le
end TheoremT.Continuum
