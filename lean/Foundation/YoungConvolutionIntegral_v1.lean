import YoungPointwise_v1
import Mathlib.Analysis.LConvolution
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped ENNReal
namespace TheoremT.Continuum

theorem lintegral_convolution_product {G : Type*} [MeasurableSpace G] [AddCommGroup G]
    [MeasurableAdd₂ G] [MeasurableNeg G] {μ : Measure G} [SFinite μ]
    [IsAddRightInvariant μ] {f g : G → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x, ∫⁻ y, f y*g (x-y) ∂μ ∂μ) = (∫⁻ y, f y ∂μ)*(∫⁻ y, g y ∂μ) := by
  rw [lintegral_lintegral_swap (by fun_prop : AEMeasurable (fun z : G×G => f z.2*g (z.1-z.2)) (μ.prod μ))]
  have hi (y : G) : (∫⁻ x, f y*g (x-y) ∂μ)=f y*(∫⁻ x, g x ∂μ) := by
    rw [lintegral_const_mul (f := fun x => g (x-y)) _ (by fun_prop),
      lintegral_sub_right_eq_self]
  simp_rw [hi]
  exact lintegral_mul_const _ hf

theorem young_convolution_lintegral_power_le {G : Type*} [MeasurableSpace G] [AddCommGroup G]
    [MeasurableAdd₂ G] [MeasurableNeg G] {μ : Measure G} [SFinite μ]
    [IsAddRightInvariant μ] [IsAddLeftInvariant μ] [IsNegInvariant μ]
    {f g : G → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    {p q r : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hpr : p ≤ r) (hqr : q ≤ r) (hs : 1/p+1/q=1+1/r) :
    (∫⁻ x, (∫⁻ y, f y*g (x-y) ∂μ)^r ∂μ) ≤
      (∫⁻ y, f y^p ∂μ)^(r/p) * (∫⁻ y, g y^q ∂μ)^(r/q) := by
  have hb : 0 ≤ r/p-1 := by rw [sub_nonneg, le_div_iff₀ hp]; simpa using hpr
  have hc : 0 ≤ r/q-1 := by rw [sub_nonneg, le_div_iff₀ hq]; simpa using hqr
  calc
    _ ≤ ∫⁻ x, (∫⁻ y, f y^p*g (x-y)^q ∂μ)*
        (∫⁻ y, f y^p ∂μ)^(r/p-1)*(∫⁻ y, g y^q ∂μ)^(r/q-1) ∂μ := by
      apply lintegral_mono
      intro x
      have ht := young_pointwise_power_le hf.aemeasurable
        (by fun_prop : AEMeasurable (fun y => g (x-y)) μ) hp hq hr hpr hqr hs
      have he : (∫⁻ y, g (x-y)^q ∂μ)=(∫⁻ y, g y^q ∂μ) :=
        lintegral_sub_left_eq_self (fun y => g y^q) x
      rwa [he] at ht
    _ = ((∫⁻ y, f y^p ∂μ)*(∫⁻ y, g y^q ∂μ))*
        (∫⁻ y, f y^p ∂μ)^(r/p-1)*(∫⁻ y, g y^q ∂μ)^(r/q-1) := by
      rw [lintegral_mul_const _ (by fun_prop), lintegral_mul_const _ (by fun_prop),
        lintegral_convolution_product (hf.pow_const p) (hg.pow_const q)]
    _ = ((∫⁻ y, f y^p ∂μ)^(1:ℝ)*(∫⁻ y, f y^p ∂μ)^(r/p-1))*
        ((∫⁻ y, g y^q ∂μ)^(1:ℝ)*(∫⁻ y, g y^q ∂μ)^(r/q-1)) := by
      simp only [ENNReal.rpow_one]
      ac_rfl
    _ = _ := by
      rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) hb,
        ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) hc]
      congr 2 <;> ring

#print axioms young_convolution_lintegral_power_le
end TheoremT.Continuum
