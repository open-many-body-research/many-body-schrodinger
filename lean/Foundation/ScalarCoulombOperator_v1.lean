import HardyCoulombSymmetry_v1

/-! The scalar atomic Coulomb graph on actual L²((R³)^N; C), without imposing
permutation symmetry. Its domain is the independently specified weak H² domain.
Classical graph selection is a mathematical operator, not a numerical solver. -/
noncomputable section
open MeasureTheory
open scoped LinearPMap
namespace TheoremT.Continuum

def scalarCoulombGraphSubmodule (N : ℕ) (Z : ℝ) :
    Submodule ℂ (SpatialL2 N × SpatialL2 N) where
  carrier := {fh | scalarHamiltonianGraph N Z fh.1 fh.2}
  zero_mem' := scalar_graph_zero N Z
  add_mem' := fun hf hg => scalar_graph_add hf hg
  smul_mem' := fun c _ hf => scalar_graph_smul c hf

def scalarCoulombOperator (N : ℕ) (Z : ℝ) : SpatialL2 N →ₗ.[ℂ] SpatialL2 N :=
  (scalarCoulombGraphSubmodule N Z).toLinearPMap

theorem scalarCoulombOperator_graph (N : ℕ) (Z : ℝ) :
    (scalarCoulombOperator N Z).graph = scalarCoulombGraphSubmodule N Z := by
  apply Submodule.toLinearPMap_graph_eq
  rintro ⟨f,h⟩ hh hf
  change f = 0 at hf
  subst f
  exact scalar_graph_unique hh (scalar_graph_zero N Z)

theorem scalarCoulombOperator_domain_iff (N : ℕ) (Z : ℝ) (f : SpatialL2 N) :
    f ∈ (scalarCoulombOperator N Z).domain ↔
      ∃ h : SpatialL2 N, scalarHamiltonianGraph N Z f h := by
  change f ∈ (scalarCoulombGraphSubmodule N Z).map (LinearMap.fst ℂ _ _) ↔ _
  constructor
  · rintro ⟨⟨f',h⟩,hg,heq⟩
    change f' = f at heq
    subst f'
    exact ⟨h,hg⟩
  · rintro ⟨h,hg⟩
    exact ⟨(f,h),hg,rfl⟩

theorem scalarCoulombOperator_domain_iff_H2 (N : ℕ) (Z : ℝ) (f : SpatialL2 N) :
    f ∈ (scalarCoulombOperator N Z).domain ↔ HasH2 f := by
  rw [scalarCoulombOperator_domain_iff]
  exact ⟨fun ⟨_,hg⟩ => scalar_graph_hasH2 hg,
    fun hf => scalar_graph_exists_of_coulombProductL2 hf (coulombProductL2_of_hasH2 Z hf)⟩

theorem scalarCoulombOperator_domain_eq_H2 (N : ℕ) (Z : ℝ) :
    ((scalarCoulombOperator N Z).domain : Set (SpatialL2 N)) = {f | HasH2 f} := by
  ext f
  exact scalarCoulombOperator_domain_iff_H2 N Z f

theorem scalarCoulombOperator_domain_dense (N : ℕ) (Z : ℝ) :
    Dense ((scalarCoulombOperator N Z).domain : Set (SpatialL2 N)) := by
  rw [scalarCoulombOperator_domain_eq_H2]
  exact weakH2_dense_in_L2 N

theorem scalarCoulombOperator_apply_graph (N : ℕ) (Z : ℝ)
    (f : (scalarCoulombOperator N Z).domain) :
    scalarHamiltonianGraph N Z f.val ((scalarCoulombOperator N Z) f) := by
  have h := (scalarCoulombOperator N Z).mem_graph f
  rw [scalarCoulombOperator_graph] at h
  exact h

theorem scalarCoulombOperator_symmetric (N : ℕ) (Z : ℝ)
    (f g : (scalarCoulombOperator N Z).domain) :
    inner ℂ (f : SpatialL2 N) ((scalarCoulombOperator N Z) g) =
      inner ℂ ((scalarCoulombOperator N Z) f) (g : SpatialL2 N) :=
  scalar_graph_symmetric (scalarCoulombOperator_apply_graph N Z f)
    (scalarCoulombOperator_apply_graph N Z g)

#print axioms scalarCoulombOperator_graph
#print axioms scalarCoulombOperator_domain_iff_H2
#print axioms scalarCoulombOperator_domain_dense
#print axioms scalarCoulombOperator_symmetric
end TheoremT.Continuum
