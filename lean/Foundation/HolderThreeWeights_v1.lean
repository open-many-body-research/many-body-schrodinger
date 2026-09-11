import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Tactic

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace TheoremT.Continuum

theorem lintegral_three_weighted_le {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g h : X → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) (hh : AEMeasurable h μ)
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hs : a+b+c=1) :
    (∫⁻ x, f x^a*g x^b*h x^c ∂μ) ≤
      (∫⁻ x, f x ∂μ)^a*(∫⁻ x, g x ∂μ)^b*(∫⁻ x, h x ∂μ)^c := by
  have ht := ENNReal.lintegral_prod_norm_pow_le (μ := μ) (Finset.univ : Finset (Fin 3))
    (f := ![f,g,h]) (p := ![a,b,c])
    (by intro i hi; fin_cases i <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] <;> assumption)
    (by simpa [Fin.sum_univ_succ,add_assoc] using hs)
    (by intro i hi; fin_cases i <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] <;> assumption)
  simpa [Fin.prod_univ_succ,mul_assoc] using ht

#print axioms lintegral_three_weighted_le
end TheoremT.Continuum
