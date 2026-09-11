import WeakPermutation_v2
import PotentialPermutation_v2
import CoulombOperatorCore_v2

/-!
Fermionic graph assembly from the actual scalar L2 multiplication condition.
Weak derivatives and the potential are proved covariant; output antisymmetry
is derived by graph uniqueness. Hardy's multiplier theorem is still required
before this becomes graph totality on the entire intended weak H2 domain.
-/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace TheoremT.Continuum

theorem scalar_graph_pullback {N : ℕ} {Z : ℝ} (π : Equiv.Perm (Fin N))
    {f h : SpatialL2 N} (hf : scalarHamiltonianGraph N Z f h) :
    scalarHamiltonianGraph N Z (pullback π f) (pullback π h) := by
  obtain ⟨d, e, hd, he, hout⟩ := hf
  let c := coordinatePermutation π
  refine ⟨fun k => pullback π (d (c.symm k)),
    fun k l => pullback π (e (c.symm k) (c.symm l)), ?_, ?_, ?_⟩
  · intro k
    simpa only [c, Equiv.apply_symm_apply] using weakPartial_pullback π (hd (c.symm k))
  · intro k l
    simpa only [c, Equiv.apply_symm_apply] using weakPartial_pullback π
      (he (c.symm k) (c.symm l))
  · have hs : ∀ᵐ x : Configuration N, ∀ k : Coordinate N,
        pullback π (e (c.symm k) (c.symm k)) x =
          e (c.symm k) (c.symm k) (permuteSpace π x) := by
      rw [ae_all_iff]
      intro k
      exact pullback_coeFn_ae π _
    have hcomp := (permuteSpace π).measurePreserving.quasiMeasurePreserving.ae hout
    filter_upwards [hs, pullback_coeFn_ae π f, pullback_coeFn_ae π h, hcomp]
      with x hsx hfx hhx houtx
    rw [hhx, hfx, houtx]
    simp_rw [hsx]
    rw [Equiv.sum_comp c.symm (fun k => e k k (permuteSpace π x)),
      coulombPotential_permuteSpace]

/-- Every scalar graph output of a fermionic input is automatically fermionic. -/
theorem scalar_outputs_fermionic {N : ℕ} {Z : ℝ} {ψ h : SpinSpace N}
    (hψ : ψ ∈ fermionicSubspace N)
    (hg : ∀ σ, scalarHamiltonianGraph N Z (ψ σ) (h σ)) :
    h ∈ fermionicSubspace N := by
  intro π σ
  have hleft := scalar_graph_pullback π (hg (permuteSpin π σ))
  rw [hψ π σ] at hleft
  exact scalar_graph_unique hleft (scalar_graph_smul (permutationSign π) (hg σ))

/-- Once each physical Coulomb product is L2, the full intended graph has a unique
fermionic output; output symmetry is proved, not a hypothesis. -/
theorem hamiltonian_graph_existsUnique_of_multiplier {N : ℕ} {Z : ℝ}
    {ψ : SpinSpace N} (hψ : ψ ∈ targetDomain N)
    (hv : ∀ σ, CoulombProductL2 Z (ψ σ)) :
    ∃! h : SpinSpace N, hamiltonianGraph N Z ψ h := by
  have hex : ∀ σ, ∃ h : SpatialL2 N, scalarHamiltonianGraph N Z (ψ σ) h :=
    fun σ => scalar_graph_exists_of_coulombProductL2 (hψ.2 σ) (hv σ)
  choose h hh using hex
  let χ : SpinSpace N := WithLp.toLp 2 h
  have hχ : ∀ σ, scalarHamiltonianGraph N Z (ψ σ) (χ σ) := hh
  have hgraph : hamiltonianGraph N Z ψ χ :=
    ⟨hψ.1, scalar_outputs_fermionic hψ.1 hχ, hχ⟩
  exact ⟨χ, hgraph, fun χ' hχ' => hamiltonian_graph_unique hχ' hgraph⟩

theorem hamiltonian_graph_existsUnique_iff {N : ℕ} {Z : ℝ} {ψ : SpinSpace N} :
    (∃! h : SpinSpace N, hamiltonianGraph N Z ψ h) ↔
      ψ ∈ targetDomain N ∧ ∀ σ, CoulombProductL2 Z (ψ σ) := by
  constructor
  · rintro ⟨h, hh, _⟩
    exact ⟨graph_input_in_targetDomain hh,
      fun σ => coulombProductL2_of_scalar_graph (hh.2.2 σ)⟩
  · rintro ⟨hψ, hv⟩
    exact hamiltonian_graph_existsUnique_of_multiplier hψ hv

/-- Exact domain characterization for the already constructed partial operator.
The missing Hardy bridge is visible as CoulombProductL2 on the right. -/
theorem coulombPartialOperator_domain_iff_H2_multiplier (N : ℕ) (Z : ℝ)
    (ψ : FermionicSpace N) :
    ψ ∈ (coulombPartialOperator N Z).domain ↔
      (∀ σ, HasH2 (ψ.val σ)) ∧ (∀ σ, CoulombProductL2 Z (ψ.val σ)) := by
  rw [coulombPartialOperator_domain_iff]
  constructor
  · rintro ⟨h, hh⟩
    exact ⟨(graph_input_in_targetDomain hh).2,
      fun σ => coulombProductL2_of_scalar_graph (hh.2.2 σ)⟩
  · rintro ⟨hH2, hv⟩
    obtain ⟨h, hh, _⟩ := hamiltonian_graph_existsUnique_of_multiplier
      (show ψ.val ∈ targetDomain N from ⟨ψ.property, hH2⟩) hv
    exact ⟨⟨h, hh.2.1⟩, hh⟩

#print axioms scalar_graph_pullback
#print axioms scalar_outputs_fermionic
#print axioms hamiltonian_graph_existsUnique_of_multiplier
#print axioms hamiltonian_graph_existsUnique_iff
#print axioms coulombPartialOperator_domain_iff_H2_multiplier
end TheoremT.Continuum
