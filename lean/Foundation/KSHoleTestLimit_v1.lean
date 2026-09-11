import KSHoleCutoff_v1
import KSSingularSetNull_v1
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace TheoremT.Continuum

theorem ksHole_tendsto_one {δ : ℕ → ℝ} (hδ : ∀ n, 0 < δ n)
    (hd : Tendsto δ atTop (𝓝 0)) {y : KSSpace} (hy : y ≠ 0) :
    Tendsto (fun n => ksHole (δ n) y) atTop (𝓝 1) := by
  have hsmall : ∀ᶠ n in atTop, δ n < ‖y‖/2 :=
    hd.eventually (gt_mem_nhds (by positivity : (0:ℝ) < ‖y‖/2))
  apply tendsto_const_nhds.congr'
  filter_upwards [hsmall] with n hn
  exact (ksHole_one_on_outer (hδ n) (by linarith)).symm

end TheoremT.Continuum
