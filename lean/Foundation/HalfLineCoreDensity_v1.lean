import HalfLineDerivativeUnique_v1
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Topology.Sequences

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace TheoremT.HalfLine

def testEmbed : Test →ₗ[ℂ] D :=
  graphMap.codRestrict domain (fun f => core.le_topologicalClosure (LinearMap.mem_range_self graphMap f))

theorem J_testEmbed (f : Test) : J (testEmbed f) = f.value := rfl
theorem dJ_testEmbed (f : Test) : dJ (testEmbed f) = f.gradient := rfl

theorem testEmbed_dense : DenseRange testEmbed := by
  rw [DenseRange, Subtype.dense_iff, ← Set.range_comp]
  change (domain : Set (E × E)) ⊆ closure (core : Set (E × E))
  exact subset_rfl

theorem exists_test_sequence (u : D) :
    ∃ f : ℕ → Test, Tendsto (fun n => testEmbed (f n)) atTop (𝓝 u) := by
  obtain ⟨v, hv, ht⟩ := mem_closure_iff_seq_limit.mp (testEmbed_dense u)
  choose f hf using hv
  exact ⟨f, by simpa only [hf] using ht⟩

#print axioms testEmbed_dense
#print axioms exists_test_sequence
end TheoremT.HalfLine
