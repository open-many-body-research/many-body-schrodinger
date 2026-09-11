import LpSupportClosed_v1
import Mathlib.Analysis.Normed.Group.Bounded

/-! Multiplication by any continuous real weight is continuous on an L2
sequence with one fixed compact support. The extension by zero outside that
compact set is bounded; actual weighted functions are identified almost everywhere. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace TheoremT.Continuum
variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E}

theorem compact_indicator_continuous_bound {K : Set E} (hK : IsCompact K)
    {χ : E → ℝ} (hχ : Continuous χ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖K.indicator χ x‖ ≤ C := by
  classical
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hχ.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ K
  · simp only [Set.indicator_of_mem hx]
    exact (hC x hx).trans (le_max_left _ _)
  · simp only [Set.indicator_of_notMem hx,norm_zero]
    exact le_max_right _ _

theorem compact_indicator_continuous_memLp_top {K : Set E} (hK : IsCompact K)
    {χ : E → ℝ} (hχ : Continuous χ) : MemLp (K.indicator χ) ⊤ μ := by
  obtain ⟨C,hCn,hCb⟩ := compact_indicator_continuous_bound hK hχ
  exact memLp_top_of_bound ((hχ.measurable.indicator hK.measurableSet).aestronglyMeasurable)
    C (Eventually.of_forall hCb)

def compactSupportWeightedL2 {K : Set E} (hK : IsCompact K)
    (χ : E → ℝ) (hχ : Continuous χ) (f : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  measureBoundedRealMul (K.indicator χ) (compact_indicator_continuous_memLp_top hK hχ) f

theorem compactSupportWeightedL2_ae {K : Set E} (hK : IsCompact K)
    (χ : E → ℝ) (hχ : Continuous χ) (f : Lp ℂ 2 μ)
    (hs : ∀ᵐ x ∂μ, x ∉ K → f x = 0) :
    compactSupportWeightedL2 hK χ hχ f =ᵐ[μ] (fun x => χ x • f x) := by
  classical
  filter_upwards [measureBoundedRealMul_ae (K.indicator χ)
    (compact_indicator_continuous_memLp_top hK hχ) f,hs] with x hx hz
  change measureBoundedRealMul _ _ f x = _
  rw [hx]
  by_cases h : x ∈ K
  · rw [Set.indicator_of_mem h]
  · simp only [Set.indicator_of_notMem h,hz h,zero_smul,smul_zero]

theorem compact_support_weight_memLp {K : Set E} (hK : IsCompact K)
    (χ : E → ℝ) (hχ : Continuous χ) (f : Lp ℂ 2 μ)
    (hs : ∀ᵐ x ∂μ, x ∉ K → f x = 0) :
    MemLp (fun x => χ x • f x) 2 μ :=
  (Lp.memLp (compactSupportWeightedL2 hK χ hχ f)).ae_eq
    (compactSupportWeightedL2_ae hK χ hχ f hs)

theorem compactSupportWeightedL2_tendsto {K : Set E} (hK : IsCompact K)
    (χ : E → ℝ) (hχ : Continuous χ)
    {g : ℕ → Lp ℂ 2 μ} {f : Lp ℂ 2 μ} (hg : Tendsto g atTop (𝓝 f)) :
    Tendsto (fun n => compactSupportWeightedL2 hK χ hχ (g n)) atTop
      (𝓝 (compactSupportWeightedL2 hK χ hχ f)) := by
  obtain ⟨C,hCn,hCb⟩ := compact_indicator_continuous_bound hK hχ
  exact measureBoundedRealMul_tendsto (K.indicator χ)
    (compact_indicator_continuous_memLp_top hK hχ) C (Eventually.of_forall hCb) hg

theorem compact_support_weight_norm_sq_tendsto {K : Set E} (hK : IsCompact K)
    (χ : E → ℝ) (hχ : Continuous χ)
    {g : ℕ → Lp ℂ 2 μ} {f : Lp ℂ 2 μ} (hg : Tendsto g atTop (𝓝 f))
    (hs : ∀ n, ∀ᵐ x ∂μ, x ∉ K → g n x = 0) :
    Tendsto (fun n => ∫ x, ‖χ x • g n x‖^2 ∂μ) atTop
      (𝓝 (∫ x, ‖χ x • f x‖^2 ∂μ)) := by
  have hf := lp_ae_zero_on_of_tendsto hK.measurableSet.compl hg hs
  have he (q : Lp ℂ 2 μ) (hq : ∀ᵐ x ∂μ, x ∉ K → q x = 0) :
      ‖compactSupportWeightedL2 hK χ hχ q‖^2 = ∫ x, ‖χ x • q x‖^2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [compactSupportWeightedL2_ae hK χ hχ q hq] with x hx
    rw [hx,real_inner_self_eq_norm_sq]
  have hh := (compactSupportWeightedL2_tendsto hK χ hχ hg).norm.pow 2
  simpa only [he _ hf,he _ (hs _)] using hh

end TheoremT.Continuum
