import IntervalPointwiseAverage_v1
import FiniteTensorMarginalBound_v1

/-! Actual finite-dimensional tensor FTC bound on a seven-coordinate box.
The mixed derivative family is linked by HasDerivAt on each coordinate line;
the coordinate pointwise inequalities are proved, not assumed. The final
integrals use the exact normalized product of restricted interval measures.
A weak-representative/density extension is a separate obligation. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators
namespace TheoremT.Continuum

def tensorClosedBox7 (a b : Fin 7 → ℝ) : Set (Fin 7 → ℝ) :=
  Set.pi Set.univ (fun i => Icc (a i) (b i))

theorem tensorClosedBox7_isClosed (a b : Fin 7 → ℝ) : IsClosed (tensorClosedBox7 a b) :=
  isClosed_set_pi (fun _ _ => isClosed_Icc)

theorem tensorClosedBox7_update {a b x : Fin 7 → ℝ}
    (hx : x ∈ tensorClosedBox7 a b) (i : Fin 7) {r : ℝ} (hr : r ∈ Icc (a i) (b i)) :
    Function.update x i r ∈ tensorClosedBox7 a b := by
  intro j hj
  by_cases hji : j = i
  · subst j
    simpa using hr
  · simpa only [Function.update_of_ne hji] using hx j hj

def tensorBoxNormField7 (a b : Fin 7 → ℝ)
    (D : Finset (Fin 7) → (Fin 7 → ℝ) → ℂ) (s : Finset (Fin 7)) :
    (Fin 7 → ℝ) → ℝ≥0∞ :=
  (tensorClosedBox7 a b).indicator (fun x => ‖D s x‖ₑ)

theorem tensorBoxNormField7_measurable (a b : Fin 7 → ℝ)
    {D : Finset (Fin 7) → (Fin 7 → ℝ) → ℂ}
    (hD : ∀ s, ContinuousOn (D s) (tensorClosedBox7 a b)) (s : Finset (Fin 7)) :
    Measurable (tensorBoxNormField7 a b D s) := by
  classical
  exact (continuous_enorm.comp_continuousOn (hD s)).measurable_piecewise
    continuousOn_const (tensorClosedBox7_isClosed a b).measurableSet

theorem tensorBoxNormField7_coordinate_average
    {a b : Fin 7 → ℝ} (hab : ∀ i, a i < b i)
    {D : Finset (Fin 7) → (Fin 7 → ℝ) → ℂ}
    (hD : ∀ s, ContinuousOn (D s) (tensorClosedBox7 a b))
    (hd : ∀ s i, i ∉ s → ∀ x ∈ tensorClosedBox7 a b,
      HasDerivAt (fun r => D s (Function.update x i r)) (D (insert i s) x) (x i)) :
    ∀ s i, i ∉ s → ∀ x,
      tensorBoxNormField7 a b D s x ≤
        lmarginal (fun j => intervalAverageMeasure (a j) (b j)) {i}
          (tensorBoxNormField7 a b D s) x +
        ENNReal.ofReal (b i-a i) *
          lmarginal (fun j => intervalAverageMeasure (a j) (b j)) {i}
            (tensorBoxNormField7 a b D (insert i s)) x := by
  intro s i hi x
  by_cases hx : x ∈ tensorClosedBox7 a b
  · have hc : Continuous (fun r : ℝ => Function.update x i r) := by fun_prop
    have hs (s : Finset (Fin 7)) :
        ContinuousOn (fun r => D s (Function.update x i r)) (Icc (a i) (b i)) :=
      (hD s).comp hc.continuousOn
        (fun r hr => tensorClosedBox7_update hx i hr)
    have hder (r : ℝ) (hr : r ∈ Icc (a i) (b i)) :
        HasDerivAt (fun t => D s (Function.update x i t))
          (D (insert i s) (Function.update x i r)) r := by
      simpa only [Function.update_idem,Function.update_self] using
        hd s i hi (Function.update x i r) (tensorClosedBox7_update hx i hr)
    have h := interval_pointwise_enorm_le_average_derivative (hab i) (hs s) (hs (insert i s))
      hder (hx i (Set.mem_univ i))
    have hint (u : Finset (Fin 7)) :
        (∫⁻ r, tensorBoxNormField7 a b D u (Function.update x i r)
          ∂intervalAverageMeasure (a i) (b i)) =
        ∫⁻ r, ‖D u (Function.update x i r)‖ₑ ∂intervalAverageMeasure (a i) (b i) := by
      simp only [intervalAverageMeasure,lintegral_smul_measure]
      congr 1
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      exact Set.indicator_of_mem (tensorClosedBox7_update hx i hr) _
    rw [lmarginal_singleton,lmarginal_singleton]
    dsimp only
    rw [hint s,hint (insert i s)]
    simpa only [tensorBoxNormField7,Set.indicator_of_mem hx,Function.update_eq_self] using h
  · rw [tensorBoxNormField7,Set.indicator_of_notMem hx]
    exact bot_le

theorem tensor_box7_pointwise_integral_bound
    {a b : Fin 7 → ℝ} (hab : ∀ i, a i < b i)
    {D : Finset (Fin 7) → (Fin 7 → ℝ) → ℂ}
    (hD : ∀ s, ContinuousOn (D s) (tensorClosedBox7 a b))
    (hd : ∀ s i, i ∉ s → ∀ x ∈ tensorClosedBox7 a b,
      HasDerivAt (fun r => D s (Function.update x i r)) (D (insert i s) x) (x i))
    {x : Fin 7 → ℝ} (hx : x ∈ tensorClosedBox7 a b) :
    ‖D ∅ x‖ₑ ≤ ∑ s ∈ (Finset.univ : Finset (Fin 7)).powerset,
      (∏ i ∈ s, ENNReal.ofReal (b i-a i)) *
        ∫⁻ y, tensorBoxNormField7 a b D s y
          ∂Measure.pi (fun i => intervalAverageMeasure (a i) (b i)) := by
  let (i : Fin 7) : IsProbabilityMeasure (intervalAverageMeasure (a i) (b i)) :=
    ⟨intervalAverageMeasure_univ (hab i)⟩
  simpa only [tensorBoxNormField7,Set.indicator_of_mem hx] using
    TensorMarginal.finite_tensor_product_bound (fun i => intervalAverageMeasure (a i) (b i))
      (fun i => ENNReal.ofReal (b i-a i)) (tensorBoxNormField7 a b D)
      (tensorBoxNormField7_measurable a b hD) (tensorBoxNormField7_coordinate_average hab hD hd) x

theorem tensor_box7_pointwise_uniform_average_bound
    {a b : Fin 7 → ℝ} (hab : ∀ i, a i < b i)
    {D : Finset (Fin 7) → (Fin 7 → ℝ) → ℂ}
    (hD : ∀ s, ContinuousOn (D s) (tensorClosedBox7 a b))
    (hd : ∀ s i, i ∉ s → ∀ x ∈ tensorClosedBox7 a b,
      HasDerivAt (fun r => D s (Function.update x i r)) (D (insert i s) x) (x i))
    {B : ℝ≥0∞}
    (hB : ∀ s, (∫⁻ y, tensorBoxNormField7 a b D s y
      ∂Measure.pi (fun i => intervalAverageMeasure (a i) (b i))) ≤ B)
    {x : Fin 7 → ℝ} (hx : x ∈ tensorClosedBox7 a b) :
    ‖D ∅ x‖ₑ ≤ (∏ i : Fin 7, (1+ENNReal.ofReal (b i-a i))) * B := by
  let (i : Fin 7) : IsProbabilityMeasure (intervalAverageMeasure (a i) (b i)) :=
    ⟨intervalAverageMeasure_univ (hab i)⟩
  simpa only [tensorBoxNormField7,Set.indicator_of_mem hx,TensorMarginal.finiteTensorCoefficient] using
    TensorMarginal.finite_tensor_uniform_bound (fun i => intervalAverageMeasure (a i) (b i))
      (fun i => ENNReal.ofReal (b i-a i)) B (tensorBoxNormField7 a b D)
      (tensorBoxNormField7_measurable a b hD) (tensorBoxNormField7_coordinate_average hab hD hd) hB x

end TheoremT.Continuum
