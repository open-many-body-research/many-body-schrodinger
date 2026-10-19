import TensorBoxPointwiseFTC_v1
import ProductBoxAverageMeasure_v1

/-! Actual seven-coordinate point evaluation from the 128 mixed {0,1} fields.
The constant depends only on the box lengths and is independent of the base
function or any derivative order. The actual coordinate derivative relations
are hypotheses; no pointwise estimate is assumed. Weak representative recovery
is a separate obligation. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators
namespace TheoremT.Continuum

theorem tensorClosedBox7_isCompact (a b : Fin 7 → ℝ) :
    IsCompact (tensorClosedBox7 a b) :=
  isCompact_univ_pi (fun _ => isCompact_Icc)

theorem tensorClosedBox7_continuous_memLp_two
    {a b : Fin 7 → ℝ} {g : (Fin 7 → ℝ) → ℂ}
    (hg : ContinuousOn g (tensorClosedBox7 a b)) :
    MemLp g 2 (volume.restrict (tensorClosedBox7 a b)) := by
  have hgi := hg.integrableOn_compact (μ := volume) (tensorClosedBox7_isCompact a b)
  exact (memLp_two_iff_integrable_sq_norm hgi.aestronglyMeasurable).mpr
    ((hg.norm.pow 2).integrableOn_compact (tensorClosedBox7_isCompact a b))

theorem tensor_box7_pointwise_L2_bound
    {a b : Fin 7 → ℝ} (hab : ∀ i, a i < b i)
    {D : Finset (Fin 7) → (Fin 7 → ℝ) → ℂ}
    (hD : ∀ s, ContinuousOn (D s) (tensorClosedBox7 a b))
    (hd : ∀ s i, i ∉ s → ∀ x ∈ tensorClosedBox7 a b,
      HasDerivAt (fun r => D s (Function.update x i r)) (D (insert i s) x) (x i))
    {M : ℝ} (hM : 0 ≤ M)
    (hL2 : ∀ s, Real.sqrt (∫ y in tensorClosedBox7 a b, ‖D s y‖^2) ≤ M)
    {x : Fin 7 → ℝ} (hx : x ∈ tensorClosedBox7 a b) :
    ‖D ∅ x‖ ≤ ((Real.sqrt (productBoxVolume a b))⁻¹ *
      ∏ i : Fin 7, (1+(b i-a i))) * M := by
  have hV := productBoxVolume_pos hab
  have hroot : 0 ≤ (Real.sqrt (productBoxVolume a b))⁻¹ :=
    inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hprod : 0 ≤ ∏ i : Fin 7, (1+(b i-a i)) :=
    Finset.prod_nonneg (fun i _ => by linarith [hab i])
  have havg : ∀ s, (∫⁻ y, tensorBoxNormField7 a b D s y
      ∂Measure.pi (fun i => intervalAverageMeasure (a i) (b i))) ≤
      ENNReal.ofReal ((Real.sqrt (productBoxVolume a b))⁻¹ * M) := by
    intro s
    apply le_trans (product_box_average_lintegral_indicator_enorm_le_L2 hab
      (tensorClosedBox7_continuous_memLp_two (hD s)))
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hL2 s) hroot)
  have h := tensor_box7_pointwise_uniform_average_bound hab hD hd havg hx
  have heq : (∏ i : Fin 7, (1+ENNReal.ofReal (b i-a i))) =
      ENNReal.ofReal (∏ i : Fin 7, (1+(b i-a i))) := by
    rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => by linarith [hab i])]
    apply Finset.prod_congr rfl
    intro i hi
    rw [ENNReal.ofReal_add (by norm_num) (by linarith [hab i])]
    simp
  rw [heq, ← ENNReal.ofReal_mul hprod] at h
  have hfinal : ENNReal.ofReal ‖D ∅ x‖ ≤ ENNReal.ofReal
      (((Real.sqrt (productBoxVolume a b))⁻¹ * ∏ i : Fin 7, (1+(b i-a i))) * M) := by
    simpa only [ofReal_norm, mul_assoc, mul_comm, mul_left_comm] using h
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (mul_nonneg hroot hprod) hM)).mp hfinal

end TheoremT.Continuum
