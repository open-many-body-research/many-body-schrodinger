import ApproximateEigenvectors_v1
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.Sequences

/-! A coercive form estimate up to a bounded finite-dimensional map makes
approximate null vectors precompact. The finite-dimensional map and the actual
form estimate are explicit hypotheses, not physical comparison conclusions. -/
noncomputable section
open Filter
open scoped Topology LinearPMap
namespace TheoremT.OperatorTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem approximate_null_cauchy_of_finite_cauchy
    (m : ℕ) (A : E →ₗ.[ℂ] E) (l : E →L[ℂ] (Fin m → ℂ)) {b C : ℝ} (hb : 0 < b) (hC : 0 ≤ C)
    (hform : ∀ x : A.domain, b * ‖(x : E)‖^2 ≤
      (inner ℂ (x : E) (A x)).re + C * ‖l (x : E)‖^2)
    (x : ℕ → A.domain) (hx : ∀ n, ‖(x n : E)‖ = 1)
    (hAx : Tendsto (fun n => ‖A (x n)‖) atTop (𝓝 0))
    (hlx : CauchySeq (fun n => l (x n : E))) :
    CauchySeq (fun n => (x n : E)) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  let δ := min 1 (b * ε^2 / (2 * (4+C)))
  have hden : 0 < 2 * (4+C) := by linarith
  have hδ : 0 < δ := lt_min zero_lt_one (div_pos (mul_pos hb (sq_pos_of_pos hε)) hden)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδb : 2 * (4+C) * δ ≤ b * ε^2 := by
    have hd := (le_div_iff₀ hden).mp (min_le_right 1 (b * ε^2 / (2*(4+C))))
    simpa only [mul_comm] using hd
  obtain ⟨nA,hnA⟩ := eventually_atTop.1 (hAx.eventually (gt_mem_nhds hδ))
  obtain ⟨nl,hnl⟩ := Metric.cauchySeq_iff.1 hlx δ hδ
  refine ⟨max nA nl,?_⟩
  intro n hn m hm
  have hnA' := hnA n (le_trans (le_max_left _ _) hn)
  have hmA' := hnA m (le_trans (le_max_left _ _) hm)
  have hl := hnl n (le_trans (le_max_right _ _) hn)
    m (le_trans (le_max_right _ _) hm)
  let w : A.domain := x n - x m
  have hw : ‖(w : E)‖ ≤ 2 := by
    change ‖(x n : E) - (x m : E)‖ ≤ 2
    exact (norm_sub_le _ _).trans (by rw [hx n,hx m]; norm_num)
  have hAw : ‖A w‖ < 2*δ := by
    have heq : A w = A (x n) - A (x m) := A.toFun.map_sub _ _
    rw [heq]
    exact (norm_sub_le _ _).trans_lt (by linarith)
  have hlw : ‖l (w : E)‖ < δ := by
    change ‖l ((x n : E) - (x m : E))‖ < δ
    rw [map_sub]
    simpa only [dist_eq_norm] using hl
  have hlsq : ‖l (w : E)‖^2 ≤ δ := by
    have hp := norm_nonneg (l (w : E))
    nlinarith
  have hq : (inner ℂ (w : E) (A w)).re < 4*δ := by
    calc
      (inner ℂ (w : E) (A w)).re ≤ ‖inner ℂ (w : E) (A w)‖ :=
        Complex.re_le_norm _
      _ ≤ ‖(w : E)‖ * ‖A w‖ := norm_inner_le_norm _ _
      _ ≤ 2 * ‖A w‖ := mul_le_mul_of_nonneg_right hw (norm_nonneg _)
      _ < 4*δ := by linarith
  have hcw := mul_le_mul_of_nonneg_left hlsq hC
  have hfw := hform w
  have hsmall : b * ‖(w : E)‖^2 < b * ε^2 := by
    nlinarith
  rw [dist_eq_norm]
  change ‖(w : E)‖ < ε
  by_contra hnot
  have he := le_of_not_gt hnot
  have hs : ‖(w : E)‖^2 < ε^2 := (mul_lt_mul_iff_right₀ hb).mp hsmall
  exact (not_lt_of_ge (pow_le_pow_left₀ hε.le he 2)) hs

#print axioms approximate_null_cauchy_of_finite_cauchy
end TheoremT.OperatorTheory
