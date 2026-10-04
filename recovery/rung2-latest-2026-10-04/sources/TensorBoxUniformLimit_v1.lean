import TensorBoxPointwiseGeometry_v1
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.MetricSpace.Cauchy

/-! Actual L2 Cauchy convergence of the 128 mixed fields implies uniform
Cauchy convergence and a continuous representative limit on a fixed closed
seven-coordinate box. The pointwise estimate is derived from tensor FTC. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace TheoremT.Continuum

theorem tensor_box_sqrt_integral_eq_Lp_norm
    {μ : Measure (Fin 7 → ℝ)} (u : Lp ℂ 2 μ) {g : (Fin 7 → ℝ) → ℂ}
    (hg : (u : (Fin 7 → ℝ) → ℂ) =ᵐ[μ] g) :
    Real.sqrt (∫ x, ‖g x‖^2 ∂μ) = ‖u‖ := by
  have hi := actual_l2_toLp_norm_sq_integral (Lp.memLp u)
  rw [Lp.toLp_coeFn] at hi
  have he : (∫ x, ‖g x‖^2 ∂μ) = ∫ x, ‖u x‖^2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [hg] with x hx
    rw [hx]
  rw [he,← hi,Real.sqrt_sq (norm_nonneg u)]

theorem tensor_box7_uniformCauchy_of_L2_Cauchy
    {a b : Fin 7 → ℝ} (hab : ∀ i, a i < b i)
    (D : ℕ → Finset (Fin 7) → (Fin 7 → ℝ) → ℂ)
    (hD : ∀ n s, ContinuousOn (D n s) (tensorClosedBox7 a b))
    (hd : ∀ n s i, i ∉ s → ∀ x ∈ tensorClosedBox7 a b,
      HasDerivAt (fun r => D n s (Function.update x i r)) (D n (insert i s) x) (x i))
    (V : ℕ → Finset (Fin 7) → Lp ℂ 2 (volume.restrict (tensorClosedBox7 a b)))
    (hV : ∀ n s, (V n s : (Fin 7 → ℝ) → ℂ) =ᵐ[volume.restrict (tensorClosedBox7 a b)] D n s)
    (hc : ∀ s, CauchySeq (fun n => V n s)) :
    UniformCauchySeqOn (fun n => D n ∅) atTop (tensorClosedBox7 a b) := by
  classical
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  let E := boxEvaluationConstant a b
  have hE : 0 < E := boxEvaluationConstant_pos hab
  let δ := ε / (2*E)
  have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) hE)
  have hc' : ∀ s, ∃ N : ℕ, ∀ n ≥ N, ∀ l ≥ N, dist (V n s) (V l s) < δ :=
    fun s => Metric.cauchySeq_iff.mp (hc s) δ hδ
  choose Ns hNs using hc'
  let N : ℕ := Finset.univ.sup Ns
  refine ⟨N,?_⟩
  intro n hn l hl x hx
  have hL2 (s : Finset (Fin 7)) :
      Real.sqrt (∫ y in tensorClosedBox7 a b, ‖D n s y-D l s y‖^2) ≤ δ := by
    have hNsN : Ns s ≤ N := Finset.le_sup (Finset.mem_univ s)
    have ha : (V n s-V l s : Lp ℂ 2 (volume.restrict (tensorClosedBox7 a b))) =ᵐ[
        volume.restrict (tensorClosedBox7 a b)] (fun y => D n s y-D l s y) := by
      filter_upwards [Lp.coeFn_sub (V n s) (V l s),hV n s,hV l s] with y hy hn hl
      simpa only [Pi.sub_apply,hn,hl] using hy
    rw [tensor_box_sqrt_integral_eq_Lp_norm (V n s-V l s) ha]
    have hb : ‖V n s-V l s‖ < δ := by
      simpa only [dist_eq_norm] using hNs s n (hNsN.trans hn) l (hNsN.trans hl)
    exact hb.le
  have hp := tensor_box7_pointwise_geometric_bound hab
    (fun s => (hD n s).sub (hD l s))
    (fun s i hi y hy => (hd n s i hi y hy).sub (hd l s i hi y hy)) hδ.le hL2 hx
  have he : E*δ < ε := by
    calc
      E*δ = ε/2 := by dsimp [δ]; field_simp
      _ < ε := half_lt_self hε
  have hp' : ‖D n ∅ x-D l ∅ x‖ ≤ E*δ := hp
  simpa only [dist_eq_norm] using hp'.trans_lt he

theorem tensor_box7_continuous_uniform_limit_of_L2_Cauchy
    {a b : Fin 7 → ℝ} (hab : ∀ i, a i < b i)
    (D : ℕ → Finset (Fin 7) → (Fin 7 → ℝ) → ℂ)
    (hD : ∀ n s, ContinuousOn (D n s) (tensorClosedBox7 a b))
    (hd : ∀ n s i, i ∉ s → ∀ x ∈ tensorClosedBox7 a b,
      HasDerivAt (fun r => D n s (Function.update x i r)) (D n (insert i s) x) (x i))
    (V : ℕ → Finset (Fin 7) → Lp ℂ 2 (volume.restrict (tensorClosedBox7 a b)))
    (hV : ∀ n s, (V n s : (Fin 7 → ℝ) → ℂ) =ᵐ[volume.restrict (tensorClosedBox7 a b)] D n s)
    (hc : ∀ s, CauchySeq (fun n => V n s)) :
    ∃ g : (Fin 7 → ℝ) → ℂ, ContinuousOn g (tensorClosedBox7 a b) ∧
      TendstoUniformlyOn (fun n => D n ∅) g atTop (tensorClosedBox7 a b) := by
  classical
  have hu := tensor_box7_uniformCauchy_of_L2_Cauchy hab D hD hd V hV hc
  have he (x : Fin 7 → ℝ) (hx : x ∈ tensorClosedBox7 a b) :
      ∃ z : ℂ, Tendsto (fun n => D n ∅ x) atTop (𝓝 z) :=
    cauchySeq_tendsto_of_complete (hu.cauchySeq hx)
  let g : (Fin 7 → ℝ) → ℂ := fun x =>
    if hx : x ∈ tensorClosedBox7 a b then Classical.choose (he x hx) else 0
  have hg (x : Fin 7 → ℝ) (hx : x ∈ tensorClosedBox7 a b) :
      Tendsto (fun n => D n ∅ x) atTop (𝓝 (g x)) := by
    dsimp only [g]
    rw [dite_eq_left hx]
    exact Classical.choose_spec (he x hx)
  have hU := hu.tendstoUniformlyOn_of_tendsto hg
  exact ⟨g,hU.continuousOn (Eventually.of_forall (fun n => hD n ∅)).frequently,hU⟩

end TheoremT.Continuum
