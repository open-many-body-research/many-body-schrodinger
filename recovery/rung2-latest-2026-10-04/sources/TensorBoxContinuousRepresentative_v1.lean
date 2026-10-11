import TensorBoxUniformLimit_v1
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! The tensor-derived uniform limit is the actual given L2 limit almost
everywhere. Thus the continuous function is a representative of the supplied
weak jet limit, not an unrelated limit chosen pointwise. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace TheoremT.Continuum

theorem tensor_box7_uniform_limit_ae_Lp_limit
    {a b : Fin 7 → ℝ}
    (f : ℕ → (Fin 7 → ℝ) → ℂ) {g : (Fin 7 → ℝ) → ℂ}
    (hU : TendstoUniformlyOn f g atTop (tensorClosedBox7 a b))
    (V : ℕ → Lp ℂ 2 (volume.restrict (tensorClosedBox7 a b)))
    (hV : ∀ n, (V n : (Fin 7 → ℝ) → ℂ) =ᵐ[volume.restrict (tensorClosedBox7 a b)] f n)
    {W : Lp ℂ 2 (volume.restrict (tensorClosedBox7 a b))}
    (hW : Tendsto V atTop (𝓝 W)) :
    (W : (Fin 7 → ℝ) → ℂ) =ᵐ[volume.restrict (tensorClosedBox7 a b)] g := by
  obtain ⟨ns,hns,hs⟩ := (tendstoInMeasure_of_tendsto_Lp hW).exists_seq_tendsto_ae
  have hAE : ∀ᵐ x ∂volume.restrict (tensorClosedBox7 a b), ∀ n, V n x = f n x := by
    rw [ae_all_iff]
    exact hV
  filter_upwards [hs,hAE,ae_restrict_mem (tensorClosedBox7_isClosed a b).measurableSet]
    with x hx he hxbox
  have hseq : Tendsto (fun n => f (ns n) x) atTop (𝓝 (W x)) := by
    simpa only [he] using hx
  exact tendsto_nhds_unique hseq ((hU.tendsto_at hxbox).comp hns.tendsto_atTop)

theorem tensor_box7_continuous_representative_of_L2_limits
    {a b : Fin 7 → ℝ} (hab : ∀ i, a i < b i)
    (D : ℕ → Finset (Fin 7) → (Fin 7 → ℝ) → ℂ)
    (hD : ∀ n s, ContinuousOn (D n s) (tensorClosedBox7 a b))
    (hd : ∀ n s i, i ∉ s → ∀ x ∈ tensorClosedBox7 a b,
      HasDerivAt (fun r => D n s (Function.update x i r)) (D n (insert i s) x) (x i))
    (V : ℕ → Finset (Fin 7) → Lp ℂ 2 (volume.restrict (tensorClosedBox7 a b)))
    (hV : ∀ n s, (V n s : (Fin 7 → ℝ) → ℂ) =ᵐ[volume.restrict (tensorClosedBox7 a b)] D n s)
    (W : Finset (Fin 7) → Lp ℂ 2 (volume.restrict (tensorClosedBox7 a b)))
    (hW : ∀ s, Tendsto (fun n => V n s) atTop (𝓝 (W s))) :
    ∃ g : (Fin 7 → ℝ) → ℂ, ContinuousOn g (tensorClosedBox7 a b) ∧
      TendstoUniformlyOn (fun n => D n ∅) g atTop (tensorClosedBox7 a b) ∧
      (W ∅ : (Fin 7 → ℝ) → ℂ) =ᵐ[volume.restrict (tensorClosedBox7 a b)] g := by
  obtain ⟨g,hg,hU⟩ := tensor_box7_continuous_uniform_limit_of_L2_Cauchy hab
    D hD hd V hV (fun s => (hW s).cauchySeq)
  exact ⟨g,hg,hU,tensor_box7_uniform_limit_ae_Lp_limit (fun n => D n ∅) hU
    (fun n => V n ∅) (fun n => hV n ∅) (hW ∅)⟩

end TheoremT.Continuum
