import TensorBoxPointwiseL2_v1
import BoxEvaluationConstant_v1

/-! Exact rectangular geometry in the seven-coordinate pointwise bound.
The named constant and its four-Y/three-T expression are fixed before the
128 actual mixed derivative fields and their L2 budget. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace TheoremT.Continuum

theorem tensor_box7_pointwise_geometric_bound
    {a b : Fin 7 → ℝ} (hab : ∀ i, a i < b i)
    {D : Finset (Fin 7) → (Fin 7 → ℝ) → ℂ}
    (hD : ∀ s, ContinuousOn (D s) (tensorClosedBox7 a b))
    (hd : ∀ s i, i ∉ s → ∀ x ∈ tensorClosedBox7 a b,
      HasDerivAt (fun r => D s (Function.update x i r)) (D (insert i s) x) (x i))
    {M : ℝ} (hM : 0 ≤ M)
    (hL2 : ∀ s, Real.sqrt (∫ y in tensorClosedBox7 a b, ‖D s y‖^2) ≤ M)
    {x : Fin 7 → ℝ} (hx : x ∈ tensorClosedBox7 a b) :
    ‖D ∅ x‖ ≤ boxEvaluationConstant a b * M :=
  tensor_box7_pointwise_L2_bound hab hD hd hM hL2 hx

theorem tensor_box7_pointwise_product_bound
    {a b : Fin 7 → ℝ} (hab : ∀ i, a i < b i)
    {D : Finset (Fin 7) → (Fin 7 → ℝ) → ℂ}
    (hD : ∀ s, ContinuousOn (D s) (tensorClosedBox7 a b))
    (hd : ∀ s i, i ∉ s → ∀ x ∈ tensorClosedBox7 a b,
      HasDerivAt (fun r => D s (Function.update x i r)) (D (insert i s) x) (x i))
    {M : ℝ} (hM : 0 ≤ M)
    (hL2 : ∀ s, Real.sqrt (∫ y in tensorClosedBox7 a b, ‖D s y‖^2) ≤ M)
    {x : Fin 7 → ℝ} (hx : x ∈ tensorClosedBox7 a b) :
    ‖D ∅ x‖ ≤ (∏ i : Fin 7,
      ((Real.sqrt (b i-a i))⁻¹ + Real.sqrt (b i-a i))) * M := by
  rw [← boxEvaluationConstant_eq_product hab]
  exact tensor_box7_pointwise_geometric_bound hab hD hd hM hL2 hx

theorem tensor_box7_pointwise_four_three_bound
    {a b : Fin 7 → ℝ} {Ly Lt : ℝ} (hLy : 0 < Ly) (hLt : 0 < Lt)
    (hlen : ∀ i, b i-a i = if i.val < 4 then Ly else Lt)
    {D : Finset (Fin 7) → (Fin 7 → ℝ) → ℂ}
    (hD : ∀ s, ContinuousOn (D s) (tensorClosedBox7 a b))
    (hd : ∀ s i, i ∉ s → ∀ x ∈ tensorClosedBox7 a b,
      HasDerivAt (fun r => D s (Function.update x i r)) (D (insert i s) x) (x i))
    {M : ℝ} (hM : 0 ≤ M)
    (hL2 : ∀ s, Real.sqrt (∫ y in tensorClosedBox7 a b, ‖D s y‖^2) ≤ M)
    {x : Fin 7 → ℝ} (hx : x ∈ tensorClosedBox7 a b) :
    ‖D ∅ x‖ ≤ (((Real.sqrt Ly)⁻¹ + Real.sqrt Ly)^4 *
      ((Real.sqrt Lt)⁻¹ + Real.sqrt Lt)^3) * M := by
  have hab : ∀ i, a i < b i := by
    intro i
    apply sub_pos.mp
    rw [hlen i]
    split_ifs <;> assumption
  rw [← boxEvaluationConstant_four_three hLy hLt hlen]
  exact tensor_box7_pointwise_geometric_bound hab hD hd hM hL2 hx

end TheoremT.Continuum
