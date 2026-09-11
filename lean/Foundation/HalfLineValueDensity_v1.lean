import HalfLineCoreDensity_v1
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-! Dense definition in the actual half-line L² space, proved by compact-test
separation, with no assumed density of a Sobolev representation. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace TheoremT.HalfLine

theorem J_range_orthogonal : J.range.orthogonal = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro u hu
  apply test_separation
  intro φ
  exact hu (J (testEmbed φ)) (LinearMap.mem_range_self J.toLinearMap (testEmbed φ))

theorem J_dense : DenseRange J := by
  have hc : J.range.topologicalClosure = ⊤ := by
    rw [← J.range.orthogonal_orthogonal_eq_closure, J_range_orthogonal,
      Submodule.bot_orthogonal_eq_top]
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr hc

#print axioms J_range_orthogonal
#print axioms J_dense
end TheoremT.HalfLine
