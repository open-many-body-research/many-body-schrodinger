import ProductL2Slices_v1

/-! Strong product-L2 convergence has a subsequence converging in slice L2 almost everywhere. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace TheoremT.ProductL2
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]

def sliceNormSqL1 (F : Lp ℂ 2 (μ.prod ν)) : Lp ℝ 1 ν :=
  (sliceNormSq_integrable F).toL1 (sliceNormSq F)

theorem sliceNormSqL1_ae (F : Lp ℂ 2 (μ.prod ν)) :
    sliceNormSqL1 F =ᵐ[ν] sliceNormSq F := (sliceNormSq_integrable F).coeFn_toL1

theorem sliceNormSqL1_norm (F : Lp ℂ 2 (μ.prod ν)) :
    ‖sliceNormSqL1 F‖ = ‖F‖ ^ 2 := by
  rw [L1.norm_eq_integral_norm]
  calc
    (∫ y, ‖sliceNormSqL1 F y‖ ∂ν) = ∫ y, sliceNormSq F y ∂ν := by
      apply integral_congr_ae
      filter_upwards [sliceNormSqL1_ae F] with y hy
      rw [hy,Real.norm_eq_abs,abs_of_nonneg (sliceNormSq_nonneg F y)]
    _ = ‖F‖ ^ 2 := sliceNormSq_integral F

theorem sliceNormSqL1_tendsto_zero (F : ℕ → Lp ℂ 2 (μ.prod ν))
    (hF : Tendsto F atTop (𝓝 0)) : Tendsto (fun n => sliceNormSqL1 (F n)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simp_rw [sliceNormSqL1_norm]
  simpa using hF.norm.pow 2

theorem exists_subseq_sliceNormSq_zero (F : ℕ → Lp ℂ 2 (μ.prod ν))
    (hF : Tendsto F atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ y ∂ν, Tendsto (fun n => sliceNormSq (F (ns n)) y) atTop (𝓝 0) := by
  obtain ⟨ns,hns,hae⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (sliceNormSqL1_tendsto_zero F hF)).exists_seq_tendsto_ae
  refine ⟨ns,hns,?_⟩
  have hcoe : ∀ᵐ y ∂ν, ∀ n : ℕ, sliceNormSqL1 (F (ns n)) y = sliceNormSq (F (ns n)) y :=
    ae_all_iff.mpr (fun n => sliceNormSqL1_ae (F (ns n)))
  filter_upwards [hae,hcoe,Lp.coeFn_zero (E := ℝ) (p := 1) (μ := ν)] with y hy hc hz
  simpa only [hc,hz,Pi.zero_apply] using hy

theorem exists_subseq_sliceLeft_tendsto (F : ℕ → Lp ℂ 2 (μ.prod ν))
    (G : Lp ℂ 2 (μ.prod ν)) (hF : Tendsto F atTop (𝓝 G)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ y ∂ν, Tendsto (fun n => sliceLeft (F (ns n)) y) atTop (𝓝 (sliceLeft G y)) := by
  have hsub : Tendsto (fun n => F n-G) atTop (𝓝 0) := by simpa using hF.sub_const G
  obtain ⟨ns,hns,hae⟩ := exists_subseq_sliceNormSq_zero (fun n => F n-G) hsub
  refine ⟨ns,hns,?_⟩
  have heq : ∀ᵐ y ∂ν, ∀ n : ℕ,
      dist (sliceLeft (F (ns n)) y) (sliceLeft G y) ^ 2 = sliceNormSq (F (ns n)-G) y :=
    ae_all_iff.mpr (fun n => sliceLeft_dist_sq_ae (F (ns n)) G)
  filter_upwards [hae,heq] with y hy heq
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hs := hy.sqrt
  simp_rw [← heq,Real.sqrt_sq (dist_nonneg)] at hs
  simpa using hs

#print axioms sliceNormSqL1_norm
#print axioms exists_subseq_sliceLeft_tendsto
end TheoremT.ProductL2
