import Mathlib.MeasureTheory.Integral.Marginal
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Pure finite tensorization of coordinate integral inequalities. The weights
and their product coefficient are fixed before the measurable function family.
All integrals are actual marginal or product Lebesgue integrals. No differential
or point-evaluation theorem is assumed beyond the displayed coordinate premise. -/
noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace TheoremT.Continuum.TensorMarginal

variable {ι : Type*} [DecidableEq ι] {X : ι → Type*}
  [∀ i, MeasurableSpace (X i)]

theorem tensor_lmarginal_add (μ : ∀ i, Measure (X i)) (s : Finset ι)
    (f g : (∀ i, X i) → ℝ≥0∞) (hf : Measurable f) :
    lmarginal μ s (fun x => f x + g x) =
      fun x => lmarginal μ s f x + lmarginal μ s g x := by
  funext x
  exact lintegral_add_left (hf.comp measurable_updateFinset) _

theorem tensor_lmarginal_const_mul (μ : ∀ i, Measure (X i)) (s : Finset ι)
    (a : ℝ≥0∞) (f : (∀ i, X i) → ℝ≥0∞) (hf : Measurable f) :
    lmarginal μ s (fun x => a * f x) = fun x => a * lmarginal μ s f x := by
  funext x
  exact lintegral_const_mul a (hf.comp measurable_updateFinset)

theorem finite_tensor_marginal_bound (μ : ∀ i, Measure (X i))
    [∀ i, SigmaFinite (μ i)] (L : ι → ℝ≥0∞)
    (F : Finset ι → (∀ i, X i) → ℝ≥0∞)
    (hF : ∀ a, Measurable (F a))
    (hstep : ∀ a i, i ∉ a → ∀ x,
      F a x ≤ lmarginal μ {i} (F a) x +
        L i * lmarginal μ {i} (F (insert i a)) x)
    (s : Finset ι) (x : ∀ i, X i) :
    F ∅ x ≤ ∑ a ∈ s.powerset, (∏ i ∈ a, L i) * lmarginal μ s (F a) x := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    calc
      F ∅ x ≤ ∑ a ∈ s.powerset, (∏ j ∈ a, L j) * lmarginal μ s (F a) x := ih
      _ ≤ ∑ a ∈ s.powerset, (∏ j ∈ a, L j) *
          (lmarginal μ (insert i s) (F a) x +
            L i * lmarginal μ (insert i s) (F (insert i a)) x) := by
        apply Finset.sum_le_sum
        intro a ha
        have hia : i ∉ a := fun hia => hi (Finset.mem_powerset.mp ha hia)
        apply mul_le_mul_right
        calc
          lmarginal μ s (F a) x ≤ lmarginal μ s (fun z =>
            lmarginal μ {i} (F a) z +
              L i * lmarginal μ {i} (F (insert i a)) z) x :=
            lmarginal_mono (hstep a i hia) x
          _ = lmarginal μ s (lmarginal μ {i} (F a)) x +
              L i * lmarginal μ s (lmarginal μ {i} (F (insert i a))) x := by
            rw [tensor_lmarginal_add μ s _ _ ((hF a).lmarginal μ),
              tensor_lmarginal_const_mul μ s _ _ ((hF (insert i a)).lmarginal μ)]
          _ = _ := by
            rw [lmarginal_singleton, lmarginal_singleton,
              ← lmarginal_insert' (F a) (hF a) hi,
              ← lmarginal_insert' (F (insert i a)) (hF (insert i a)) hi]
      _ = ∑ a ∈ (insert i s).powerset,
          (∏ j ∈ a, L j) * lmarginal μ (insert i s) (F a) x := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, Finset.sum_powerset_insert hi]
        congr 1
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.prod_insert (fun hia => hi (Finset.mem_powerset.mp ha hia))]
        ac_rfl

theorem finite_tensor_product_bound [Fintype ι] (μ : ∀ i, Measure (X i))
    [∀ i, SigmaFinite (μ i)] (L : ι → ℝ≥0∞)
    (F : Finset ι → (∀ i, X i) → ℝ≥0∞)
    (hF : ∀ a, Measurable (F a))
    (hstep : ∀ a i, i ∉ a → ∀ x,
      F a x ≤ lmarginal μ {i} (F a) x +
        L i * lmarginal μ {i} (F (insert i a)) x)
    (x : ∀ i, X i) :
    F ∅ x ≤ ∑ a ∈ (Finset.univ : Finset ι).powerset,
      (∏ i ∈ a, L i) * ∫⁻ y, F a y ∂Measure.pi μ := by
  simpa only [lmarginal_univ] using finite_tensor_marginal_bound μ L F hF hstep
    Finset.univ x

def finiteTensorCoefficient [Fintype ι] (L : ι → ℝ≥0∞) : ℝ≥0∞ :=
  ∏ i, (1 + L i)

theorem finite_tensor_uniform_bound [Fintype ι] (μ : ∀ i, Measure (X i))
    [∀ i, SigmaFinite (μ i)] (L : ι → ℝ≥0∞) (B : ℝ≥0∞)
    (F : Finset ι → (∀ i, X i) → ℝ≥0∞)
    (hF : ∀ a, Measurable (F a))
    (hstep : ∀ a i, i ∉ a → ∀ x,
      F a x ≤ lmarginal μ {i} (F a) x +
        L i * lmarginal μ {i} (F (insert i a)) x)
    (hbound : ∀ a, (∫⁻ y, F a y ∂Measure.pi μ) ≤ B)
    (x : ∀ i, X i) : F ∅ x ≤ finiteTensorCoefficient L * B := by
  calc
    F ∅ x ≤ ∑ a ∈ (Finset.univ : Finset ι).powerset,
        (∏ i ∈ a, L i) * ∫⁻ y, F a y ∂Measure.pi μ :=
      finite_tensor_product_bound μ L F hF hstep x
    _ ≤ ∑ a ∈ (Finset.univ : Finset ι).powerset, (∏ i ∈ a, L i) * B := by
      exact Finset.sum_le_sum fun a _ => mul_le_mul_right (hbound a) _
    _ = finiteTensorCoefficient L * B := by
      rw [← Finset.sum_mul, ← Finset.prod_one_add]
      rfl

end TheoremT.Continuum.TensorMarginal
