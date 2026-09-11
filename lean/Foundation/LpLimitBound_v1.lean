import L2FatouBound_v1
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! Lower semicontinuity of every extended Lp norm along an actual L2 limit,
with a convergent real upper-bound sequence. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal ENNReal
namespace TheoremT.Continuum

theorem eLpNorm_le_of_L2_tendsto_bound {N : ℕ} (g : ℕ → SpatialL2 N)
    {f : SpatialL2 N} (hg : Tendsto g atTop (𝓝 f)) {q : ℝ≥0∞}
    (c : ℕ → ℝ) {C : ℝ} (hc : Tendsto c atTop (𝓝 C))
    (hb : ∀ n, eLpNorm (g n) q volume ≤ ENNReal.ofReal (c n)) :
    eLpNorm f q volume ≤ ENNReal.ofReal C := by
  apply le_of_forall_gt
  intro b hbC
  obtain ⟨b',hb',hb'b⟩ := exists_between hbC
  have he : ∀ᶠ n in atTop, ENNReal.ofReal (c n) < b' :=
    (ENNReal.continuous_ofReal.tendsto C |>.comp hc).eventually (gt_mem_nhds hb')
  exact (eLpNorm_le_of_tendstoInMeasure
    (he.mono (fun n hn => (hb n).trans hn.le))
    (tendstoInMeasure_of_tendsto_Lp hg) (fun n => Lp.aestronglyMeasurable (g n))).trans_lt hb'b

#print axioms eLpNorm_le_of_L2_tendsto_bound
end TheoremT.Continuum
