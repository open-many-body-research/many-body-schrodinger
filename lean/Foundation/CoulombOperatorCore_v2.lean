import WeakDomainAlgebra_v2
import Mathlib.LinearAlgebra.LinearPMap

/-!
The actual weak Coulomb graph is linear and defines a partial linear operator.
Its domain is precisely the inputs for which the specified graph has output;
equality with all intended fermionic H2 inputs still requires F02. Neither
density nor self-adjointness is asserted here. Classical choice selects the
unique mathematical graph value and is NOT an executable numerical algorithm.
-/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace TheoremT.Continuum

theorem scalar_graph_zero (N : ℕ) (Z : ℝ) :
    scalarHamiltonianGraph N Z 0 0 := by
  refine ⟨fun _ => 0, fun _ _ => 0, weakPartial_zero,
    fun _ l => weakPartial_zero l, ?_⟩
  filter_upwards with x
  simp

theorem scalar_graph_add {N : ℕ} {Z : ℝ} {f g h j : SpatialL2 N}
    (hf : scalarHamiltonianGraph N Z f h)
    (hg : scalarHamiltonianGraph N Z g j) :
    scalarHamiltonianGraph N Z (f + g) (h + j) := by
  obtain ⟨df, ef, hdf, hef, hf⟩ := hf
  obtain ⟨dg, eg, hdg, heg, hg⟩ := hg
  refine ⟨fun k => df k + dg k, fun k l => ef k l + eg k l,
    fun k => weakPartial_add (hdf k) (hdg k),
    fun k l => weakPartial_add (hef k l) (heg k l), ?_⟩
  have hs : ∀ᵐ x : Configuration N, ∀ k : Coordinate N,
      (ef k k + eg k k) x = ef k k x + eg k k x := by
    rw [ae_all_iff]
    intro k
    exact Lp.coeFn_add _ _
  filter_upwards [hf, hg, Lp.coeFn_add f g, Lp.coeFn_add h j, hs] with x hfx hgx hfg hhj hsx
  simp only [Pi.add_apply] at hfg hhj
  rw [hhj, hfg, hfx, hgx]
  simp_rw [hsx]
  rw [Finset.sum_add_distrib]
  ring

theorem scalar_graph_smul {N : ℕ} {Z : ℝ} (c : ℂ) {f h : SpatialL2 N}
    (hf : scalarHamiltonianGraph N Z f h) :
    scalarHamiltonianGraph N Z (c • f) (c • h) := by
  obtain ⟨d, e, hd, he, hf⟩ := hf
  refine ⟨fun k => c • d k, fun k l => c • e k l,
    fun k => weakPartial_smul c (hd k),
    fun k l => weakPartial_smul c (he k l), ?_⟩
  have hs : ∀ᵐ x : Configuration N, ∀ k : Coordinate N,
      (c • e k k) x = c * e k k x := by
    rw [ae_all_iff]
    intro k
    exact Lp.coeFn_smul _ _
  filter_upwards [hf, Lp.coeFn_smul c f, Lp.coeFn_smul c h, hs] with x hfx hcf hch hsx
  simp only [Pi.smul_apply, smul_eq_mul] at hcf hch
  rw [hch, hcf, hfx]
  simp_rw [hsx]
  rw [← Finset.mul_sum]
  ring

theorem hamiltonian_graph_zero (N : ℕ) (Z : ℝ) : hamiltonianGraph N Z 0 0 :=
  ⟨(fermionicSubspace N).zero_mem, (fermionicSubspace N).zero_mem,
    fun _ => scalar_graph_zero N Z⟩

theorem hamiltonian_graph_add {N : ℕ} {Z : ℝ} {f g h j : SpinSpace N}
    (hf : hamiltonianGraph N Z f h) (hg : hamiltonianGraph N Z g j) :
    hamiltonianGraph N Z (f + g) (h + j) :=
  ⟨(fermionicSubspace N).add_mem hf.1 hg.1,
    (fermionicSubspace N).add_mem hf.2.1 hg.2.1,
    fun σ => scalar_graph_add (hf.2.2 σ) (hg.2.2 σ)⟩

theorem hamiltonian_graph_smul {N : ℕ} {Z : ℝ} (c : ℂ) {f h : SpinSpace N}
    (hf : hamiltonianGraph N Z f h) :
    hamiltonianGraph N Z (c • f) (c • h) :=
  ⟨(fermionicSubspace N).smul_mem c hf.1,
    (fermionicSubspace N).smul_mem c hf.2.1,
    fun σ => scalar_graph_smul c (hf.2.2 σ)⟩

/-- The actual graph as a submodule of the full fermionic Hilbert space squared. -/
def coulombGraphSubmodule (N : ℕ) (Z : ℝ) :
    Submodule ℂ (FermionicSpace N × FermionicSpace N) where
  carrier := {fh | hamiltonianGraph N Z fh.1.val fh.2.val}
  zero_mem' := hamiltonian_graph_zero N Z
  add_mem' := fun hf hg => hamiltonian_graph_add hf hg
  smul_mem' := fun c _ hf => hamiltonian_graph_smul c hf

theorem coulombGraphSubmodule_singleValued (N : ℕ) (Z : ℝ)
    {h : FermionicSpace N} (hh : (0, h) ∈ coulombGraphSubmodule N Z) : h = 0 := by
  apply Subtype.ext
  exact hamiltonian_graph_unique hh (hamiltonian_graph_zero N Z)

/-- Partial operator induced by the concrete weak graph, without claiming totality on H2. -/
def coulombPartialOperator (N : ℕ) (Z : ℝ) :
    FermionicSpace N →ₗ.[ℂ] FermionicSpace N :=
  (coulombGraphSubmodule N Z).toLinearPMap

theorem coulombPartialOperator_graph (N : ℕ) (Z : ℝ) :
    (coulombPartialOperator N Z).graph = coulombGraphSubmodule N Z := by
  apply Submodule.toLinearPMap_graph_eq
  rintro ⟨f, h⟩ hh hf
  change f = 0 at hf
  subst f
  exact coulombGraphSubmodule_singleValued N Z hh

theorem coulombPartialOperator_domain_iff (N : ℕ) (Z : ℝ) (f : FermionicSpace N) :
    f ∈ (coulombPartialOperator N Z).domain ↔
      ∃ h : FermionicSpace N, hamiltonianGraph N Z f.val h.val := by
  change f ∈ (coulombGraphSubmodule N Z).map (LinearMap.fst ℂ _ _) ↔ _
  constructor
  · rintro ⟨⟨f', h⟩, hgraph, heq⟩
    change f' = f at heq
    subst f'
    exact ⟨h, hgraph⟩
  · rintro ⟨h, hh⟩
    exact ⟨(f, h), hh, rfl⟩

theorem coulombPartialOperator_domain_subset_H2 (N : ℕ) (Z : ℝ)
    (f : (coulombPartialOperator N Z).domain) : f.val.val ∈ targetDomain N := by
  obtain ⟨h, hh⟩ := (coulombPartialOperator_domain_iff N Z f.val).1 f.property
  exact graph_input_in_targetDomain hh

#print axioms scalar_graph_zero
#print axioms scalar_graph_add
#print axioms scalar_graph_smul
#print axioms hamiltonian_graph_add
#print axioms hamiltonian_graph_smul
#print axioms coulombPartialOperator_graph
#print axioms coulombPartialOperator_domain_iff
#print axioms coulombPartialOperator_domain_subset_H2
end TheoremT.Continuum
