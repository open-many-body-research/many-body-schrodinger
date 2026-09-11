import PartialMollifierConvergence_v1
import MeasureBoundedRealMultiplier_v1

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace TheoremT.Continuum
variable {Y T : Type*}
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
  [MeasurableSpace T] [BorelSpace T]

theorem product_compact_multiplier_exists_norm_bound
    {χ : Y × T → ℝ} (hχ : Continuous χ) (hcχ : HasCompactSupport χ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p, ‖χ p‖ ≤ C := by
  obtain ⟨C,hC⟩ := hcχ.exists_bound_of_continuousOn hχ.continuousOn
  refine ⟨max C 0,le_max_right _ _,fun p => ?_⟩
  by_cases hp : p ∈ tsupport χ
  · exact (hC p hp).trans (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hp,norm_zero]
    exact le_max_right _ _

theorem product_compact_multiplier_tendsto_of_eventual_ae
    {χ : Y × T → ℝ} (hχ : Continuous χ) (hcχ : HasCompactSupport χ)
    {u g : ℕ → Lp ℂ 2 (volume : Measure (Y × T))}
    {f U : Lp ℂ 2 (volume : Measure (Y × T))}
    (hg : Tendsto g atTop (𝓝 f))
    (hu : ∀ᶠ n : ℕ in atTop, u n =ᵐ[volume] (fun p => χ p • g n p))
    (hU : U =ᵐ[volume] (fun p => χ p • f p)) : Tendsto u atTop (𝓝 U) := by
  have ht : MemLp χ ⊤ volume := hχ.memLp_top_of_hasCompactSupport hcχ volume
  obtain ⟨C,_,hC⟩ := product_compact_multiplier_exists_norm_bound hχ hcχ
  have heU : U = measureBoundedRealMul χ ht f :=
    Lp.ext (hU.trans (measureBoundedRealMul_ae χ ht f).symm)
  have he : (fun n => measureBoundedRealMul χ ht (g n)) =ᶠ[atTop] u := by
    filter_upwards [hu] with n hn
    exact (Lp.ext (hn.trans (measureBoundedRealMul_ae χ ht (g n)).symm)).symm
  rw [heU]
  exact (measureBoundedRealMul_tendsto χ ht C (Filter.Eventually.of_forall hC) hg).congr' he

theorem partialMollify_cutoff_tendsto_of_eventual_ae
    {χ : Y × T → ℝ} (hχ : Continuous χ) (hcχ : HasCompactSupport χ)
    (f : Lp ℂ 2 (volume : Measure (Y × T)))
    {u : ℕ → Lp ℂ 2 (volume : Measure (Y × T))}
    {U : Lp ℂ 2 (volume : Measure (Y × T))}
    (hu : ∀ᶠ n : ℕ in atTop, u n =ᵐ[volume] (fun p => χ p • partialMollifyLp n f p))
    (hU : U =ᵐ[volume] (fun p => χ p • f p)) : Tendsto u atTop (𝓝 U) :=
  product_compact_multiplier_tendsto_of_eventual_ae hχ hcχ (partialMollifyLp_tendsto f) hu hU

#print axioms product_compact_multiplier_tendsto_of_eventual_ae
#print axioms partialMollify_cutoff_tendsto_of_eventual_ae
end TheoremT.Continuum
