import ConfigurationL2Dominated_v1

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace TheoremT.Continuum

theorem configuration_L2_tendsto_dominated {N : ℕ} (F : ℕ → SpatialL2 N) (f : SpatialL2 N)
    (bound : Configuration N → ℝ) (hb : MemLp bound 2 volume)
    (hFn : ∀ n, ∀ᵐ x, ‖F n x‖ ≤ ‖bound x‖)
    (hfn : ∀ᵐ x, ‖f x‖ ≤ ‖bound x‖)
    (ht : ∀ᵐ x, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    Tendsto F atTop (𝓝 f) := by
  simpa only [Lp.toLp_coeFn] using configuration_toLp_tendsto_dominated
    (fun n => Lp.memLp (F n)) (Lp.memLp f) hb hFn hfn ht

#print axioms configuration_L2_tendsto_dominated
end TheoremT.Continuum
