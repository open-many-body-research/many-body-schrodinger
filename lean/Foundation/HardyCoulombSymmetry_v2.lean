import HardyCoulombSymmetry_v1
import PotentialSpinSymmetry_v2

/-! The existing partial operator is densely defined and symmetric on exactly
the independently defined fermionic weak H² domain. Self-adjointness is separate. -/
noncomputable section
open MeasureTheory
namespace TheoremT.Continuum

theorem coulombPartialOperator_apply_graph (N : ℕ) (Z : ℝ)
    (f : (coulombPartialOperator N Z).domain) :
    hamiltonianGraph N Z f.val.val ((coulombPartialOperator N Z) f).val := by
  have h := (coulombPartialOperator N Z).mem_graph f
  rw [coulombPartialOperator_graph] at h
  exact h

/-- Exact complex symmetry of the concrete operator on its full weak H² domain. -/
theorem coulombPartialOperator_symmetric (N : ℕ) (Z : ℝ)
    (f g : (coulombPartialOperator N Z).domain) :
    inner ℂ (f : FermionicSpace N) ((coulombPartialOperator N Z) g) =
      inner ℂ ((coulombPartialOperator N Z) f) (g : FermionicSpace N) := by
  change inner ℂ f.val.val ((coulombPartialOperator N Z) g).val =
    inner ℂ ((coulombPartialOperator N Z) f).val g.val.val
  exact hamiltonian_graph_symmetric (coulombPartialOperator_apply_graph N Z f)
    (coulombPartialOperator_apply_graph N Z g)

/-- The shared continuum foundation now supplies exact domain, dense definition,
and complex symmetry. This statement does not assert self-adjointness. -/
theorem coulombPartialOperator_dense_H2_symmetric (N : ℕ) (Z : ℝ) :
    (∀ f : FermionicSpace N, f ∈ (coulombPartialOperator N Z).domain ↔
      f.val ∈ targetDomain N) ∧
    Dense ((coulombPartialOperator N Z).domain : Set (FermionicSpace N)) ∧
    ∀ f g : (coulombPartialOperator N Z).domain,
      inner ℂ (f : FermionicSpace N) ((coulombPartialOperator N Z) g) =
        inner ℂ ((coulombPartialOperator N Z) f) (g : FermionicSpace N) := by
  refine ⟨?_, coulombPartialOperator_domain_dense N Z, coulombPartialOperator_symmetric N Z⟩
  intro f
  rw [coulombPartialOperator_domain_iff_H2]
  simp only [targetDomain, Set.mem_setOf_eq, f.property, true_and]

#print axioms coulombPartialOperator_apply_graph
#print axioms coulombPartialOperator_symmetric
#print axioms coulombPartialOperator_dense_H2_symmetric
end TheoremT.Continuum
