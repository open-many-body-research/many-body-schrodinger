import MeasureBoundedRealMultiplier_v1

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace TheoremT.Continuum
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem lp_ae_zero_on_of_tendsto {S : Set α} (hS : MeasurableSet S)
    {g : ℕ → Lp ℂ 2 μ} {f : Lp ℂ 2 μ} (hg : Tendsto g atTop (𝓝 f))
    (hs : ∀ n, ∀ᵐ x ∂μ, x ∈ S → g n x = 0) :
    ∀ᵐ x ∂μ, x ∈ S → f x = 0 := by
  classical
  let χ : α → ℝ := S.indicator (fun _ => 1)
  have hb : ∀ᵐ x ∂μ, ‖χ x‖ ≤ 1 := Eventually.of_forall (fun x => by
    by_cases hx : x ∈ S <;> simp [χ,hx])
  have hm : MemLp χ ⊤ μ := memLp_top_of_bound
    ((measurable_const.indicator hS).aestronglyMeasurable) 1 hb
  have hz (n : ℕ) : measureBoundedRealMul χ hm (g n) = 0 := by
    apply Lp.ext
    filter_upwards [measureBoundedRealMul_ae χ hm (g n),hs n,Lp.coeFn_zero ℂ 2 μ] with x hx hy hz
    rw [hx,hz]
    by_cases hxs : x ∈ S
    · simp [χ,hxs,hy hxs]
    · simp [χ,hxs]
  have ht := measureBoundedRealMul_tendsto χ hm 1 hb hg
  simp only [hz] at ht
  have hf0 : measureBoundedRealMul χ hm f = 0 :=
    (tendsto_nhds_unique ht tendsto_const_nhds)
  have he := measureBoundedRealMul_ae χ hm f
  rw [hf0] at he
  filter_upwards [he,Lp.coeFn_zero ℂ 2 μ] with x hx hz hxs
  rw [hz] at hx
  simpa [χ,hxs] using hx.symm

#print axioms lp_ae_zero_on_of_tendsto
end TheoremT.Continuum
