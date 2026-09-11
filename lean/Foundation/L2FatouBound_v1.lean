import CutoffConvergence_v2
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-! An actual a.e. limit of uniformly bounded L² representatives remains L².
This uses Mathlib's Fatou lemma and records a norm bound for the actual class. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace TheoremT.Continuum

theorem memLp_of_ae_tendsto_L2_bounded {N : ℕ} (f : ℕ → SpatialL2 N)
    (u : Configuration N → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n, ‖f n‖ ≤ C)
    (ht : ∀ᵐ x, Tendsto (fun n : ℕ => f n x) atTop (𝓝 (u x))) :
    ∃ hu : MemLp u 2 volume, ‖hu.toLp u‖ ≤ C := by
  have hu : AEStronglyMeasurable u volume :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => Lp.aestronglyMeasurable (f n)) ht
  have hnorm : eLpNorm u 2 volume ≤ ENNReal.ofReal C := by
    apply Lp.eLpNorm_le_of_ae_tendsto _ (fun n => Lp.aestronglyMeasurable (f n)) ht
    apply Eventually.of_forall
    intro n
    rw [← Lp.enorm_def,← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hb n)
  have hm : MemLp u 2 volume := ⟨hu,hnorm.trans_lt ENNReal.ofReal_lt_top⟩
  refine ⟨hm,?_⟩
  rw [Lp.norm_toLp]
  exact (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hnorm)
    ENNReal.ofReal_ne_top).mpr hnorm |>.trans_eq (ENNReal.toReal_ofReal hC)

#print axioms memLp_of_ae_tendsto_L2_bounded
end TheoremT.Continuum
