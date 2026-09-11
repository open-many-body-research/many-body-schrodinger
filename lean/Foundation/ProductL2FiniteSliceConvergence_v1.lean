import ProductL2SliceConvergence_v1

/-! One common subsequence for finitely many actual L2 slices. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace TheoremT.ProductL2
variable {X Y I : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]

theorem exists_subseq_sliceLeft_tendsto_finset (s : Finset I)
    (F : ℕ → I → Lp ℂ 2 (μ.prod ν)) (G : I → Lp ℂ 2 (μ.prod ν))
    (hF : ∀ i, Tendsto (fun n => F n i) atTop (𝓝 (G i))) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ y ∂ν, ∀ i ∈ s,
      Tendsto (fun n => sliceLeft (F (ns n) i) y) atTop (𝓝 (sliceLeft (G i) y)) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨id,strictMono_id,Filter.Eventually.of_forall (by simp)⟩
  | @insert i s hi ih =>
    obtain ⟨ns,hns,hs⟩ := ih
    obtain ⟨ms,hms,hi⟩ := exists_subseq_sliceLeft_tendsto (fun n => F (ns n) i) (G i)
      ((hF i).comp hns.tendsto_atTop)
    refine ⟨ns ∘ ms,hns.comp hms,?_⟩
    filter_upwards [hs,hi] with y hs hi
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hi
    · exact (hs j hj).comp hms.tendsto_atTop

theorem exists_subseq_sliceLeft_tendsto_finite [Fintype I]
    (F : ℕ → I → Lp ℂ 2 (μ.prod ν)) (G : I → Lp ℂ 2 (μ.prod ν))
    (hF : ∀ i, Tendsto (fun n => F n i) atTop (𝓝 (G i))) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ y ∂ν, ∀ i,
      Tendsto (fun n => sliceLeft (F (ns n) i) y) atTop (𝓝 (sliceLeft (G i) y)) := by
  simpa using exists_subseq_sliceLeft_tendsto_finset Finset.univ F G hF

#print axioms exists_subseq_sliceLeft_tendsto_finite
end TheoremT.ProductL2
