import WeakCoulombL2_v2
import FermionicGraphAssembly_v2
import FermionicDensity_v2

/-! The physical Coulomb graph has exactly the intended weak-H2 fermionic
domain for every finite electron count and real charge. This proves existence,
uniqueness, exact domain and dense definition. It does not assert symmetry,
self-adjointness or spectral identification. -/
noncomputable section
open MeasureTheory
namespace TheoremT.Continuum

/-- Every intended input has one and only one actual fermionic Hamiltonian
output. The Coulomb multiplication and output symmetry premises are discharged. -/
theorem hamiltonian_graph_existsUnique_of_targetDomain {N : ℕ} {Z : ℝ}
    {ψ : SpinSpace N} (hψ : ψ ∈ targetDomain N) :
    ∃! h : SpinSpace N, hamiltonianGraph N Z ψ h :=
  hamiltonian_graph_existsUnique_of_multiplier hψ
    (fun σ => coulombProductL2_of_hasH2 Z (hψ.2 σ))

theorem hamiltonian_graph_existsUnique_iff_targetDomain {N : ℕ} {Z : ℝ}
    {ψ : SpinSpace N} :
    (∃! h : SpinSpace N, hamiltonianGraph N Z ψ h) ↔ ψ ∈ targetDomain N := by
  constructor
  · rintro ⟨h, hh, _⟩
    exact graph_input_in_targetDomain hh
  · exact hamiltonian_graph_existsUnique_of_targetDomain

theorem coulombPartialOperator_domain_iff_H2 (N : ℕ) (Z : ℝ)
    (ψ : FermionicSpace N) :
    ψ ∈ (coulombPartialOperator N Z).domain ↔ ∀ σ, HasH2 (ψ.val σ) := by
  rw [coulombPartialOperator_domain_iff_H2_multiplier]
  exact ⟨And.left, fun h => ⟨h, fun σ => coulombProductL2_of_hasH2 Z (h σ)⟩⟩

/-- Equality of actual operator domains as sets in the genuine fermionic L2
Hilbert space, not a new strengthened definition of the intended domain. -/
theorem coulombPartialOperator_domain_eq_H2 (N : ℕ) (Z : ℝ) :
    ((coulombPartialOperator N Z).domain : Set (FermionicSpace N)) =
      {ψ | ∀ σ, HasH2 (ψ.val σ)} := by
  ext ψ
  exact coulombPartialOperator_domain_iff_H2 N Z ψ

theorem coulombPartialOperator_domain_dense (N : ℕ) (Z : ℝ) :
    Dense ((coulombPartialOperator N Z).domain : Set (FermionicSpace N)) := by
  rw [coulombPartialOperator_domain_eq_H2]
  exact fermionic_weakH2_dense N

#print axioms hamiltonian_graph_existsUnique_of_targetDomain
#print axioms hamiltonian_graph_existsUnique_iff_targetDomain
#print axioms coulombPartialOperator_domain_iff_H2
#print axioms coulombPartialOperator_domain_eq_H2
#print axioms coulombPartialOperator_domain_dense
end TheoremT.Continuum
