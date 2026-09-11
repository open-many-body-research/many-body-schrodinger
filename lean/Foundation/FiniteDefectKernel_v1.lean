import FiniteDefectCauchy_v1

/-! A finite-dimensional defect in coercivity forces attainment of an approximate
null sequence for a closed operator. All operator and comparison data are
explicit; this is not yet the physical hydrogenic comparison. -/
noncomputable section
open Filter
open scoped Topology LinearPMap
namespace TheoremT.OperatorTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem closed_operator_kernel_of_finite_defect
    (m : ℕ) (A : E →ₗ.[ℂ] E) (hA : A.IsClosed) (l : E →L[ℂ] (Fin m → ℂ))
    {b C : ℝ} (hb : 0 < b) (hC : 0 ≤ C)
    (hform : ∀ x : A.domain, b * ‖(x : E)‖^2 ≤
      (inner ℂ (x : E) (A x)).re + C * ‖l (x : E)‖^2)
    (x : ℕ → A.domain) (hx : ∀ n, ‖(x n : E)‖ = 1)
    (hAx : Tendsto (fun n => ‖A (x n)‖) atTop (𝓝 0)) :
    ∃ u : A.domain, ‖(u : E)‖ = 1 ∧ A u = 0 := by
  have hlbounded : ∀ n, l (x n : E) ∈ Metric.closedBall (0 : Fin m → ℂ) ‖l‖ := by
    intro n
    rw [Metric.mem_closedBall,dist_zero_right]
    exact (l.le_opNorm (x n : E)).trans_eq (by rw [hx n,mul_one])
  obtain ⟨c,hc,φ,hφ,hconv⟩ := (isCompact_closedBall (0 : Fin m → ℂ) ‖l‖).tendsto_subseq hlbounded
  let y : ℕ → A.domain := fun n => x (φ n)
  have hy : ∀ n, ‖(y n : E)‖ = 1 := fun n => hx (φ n)
  have hAy : Tendsto (fun n => ‖A (y n)‖) atTop (𝓝 0) :=
    hAx.comp hφ.tendsto_atTop
  have hly : CauchySeq (fun n => l (y n : E)) := hconv.cauchySeq
  have hyC := approximate_null_cauchy_of_finite_cauchy m A l hb hC hform y hy hAy hly
  obtain ⟨u,hu⟩ := cauchySeq_tendsto_of_complete hyC
  have hAu : Tendsto (fun n => A (y n)) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hAy
  have hg : (u,0) ∈ A.graph := hA.mem_of_tendsto (hu.prodMk_nhds hAu)
    (Eventually.of_forall (fun n => A.mem_graph (y n)))
  have hum : u ∈ A.domain := LinearPMap.mem_domain_of_mem_graph hg
  refine ⟨⟨u,hum⟩,?_,?_⟩
  · have hn : Tendsto (fun n => ‖(y n : E)‖) atTop (𝓝 (1 : ℝ)) := by
      simp only [hy]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique hu.norm hn
  · exact ((LinearPMap.image_iff hum).2 hg).symm

#print axioms closed_operator_kernel_of_finite_defect
end TheoremT.OperatorTheory
