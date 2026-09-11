import FermionicAction_v2
import SmoothL2Density_v2

/-! A concrete antisymmetrizer and dense intended fermionic weak H2 domain.
Density is proved via a continuous surjective projection preserving H2,
not inferred by intersecting an arbitrary dense set with a closed subspace.
No Hamiltonian graph-norm core or self-adjointness is asserted here.
-/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace TheoremT.Continuum

local instance permutationCardInvertible (N : ℕ) :
    Invertible (Fintype.card (Equiv.Perm (Fin N)) : ℂ) :=
  invertibleOfNonzero (by exact_mod_cast Fintype.card_ne_zero)

def fermionicProjection (N : ℕ) : SpinSpace N →ₗ[ℂ] SpinSpace N :=
  (signedSpinRepresentation N).averageMap

theorem fermionicProjection_apply (N : ℕ) (ψ : SpinSpace N) :
    fermionicProjection N ψ =
      (Fintype.card (Equiv.Perm (Fin N)) : ℂ)⁻¹ •
        ∑ π : Equiv.Perm (Fin N), permutationSign π • spinAction π ψ := by
  simp [fermionicProjection, Representation.averageMap, GroupAlgebra.average,
    map_sum, signedSpinRepresentation]

theorem fermionicProjection_mem (N : ℕ) (ψ : SpinSpace N) :
    fermionicProjection N ψ ∈ fermionicSubspace N := by
  rw [← signedSpinRepresentation_invariants]
  exact Representation.averageMap_invariant _ ψ

theorem fermionicProjection_id {N : ℕ} {ψ : SpinSpace N}
    (hψ : ψ ∈ fermionicSubspace N) : fermionicProjection N ψ = ψ := by
  apply Representation.averageMap_id
  rwa [signedSpinRepresentation_invariants]

theorem fermionicProjection_continuous (N : ℕ) :
    Continuous (fermionicProjection N : SpinSpace N → SpinSpace N) := by
  have heq : (fermionicProjection N : SpinSpace N → SpinSpace N) =
      fun ψ => (Fintype.card (Equiv.Perm (Fin N)) : ℂ)⁻¹ •
        ∑ π : Equiv.Perm (Fin N), permutationSign π • spinAction π ψ :=
    funext (fermionicProjection_apply N)
  rw [heq]
  have hs : Continuous (fun ψ : SpinSpace N =>
      ∑ π : Equiv.Perm (Fin N), permutationSign π • spinAction π ψ) :=
    continuous_finsetSum Finset.univ (fun π _ =>
      (spinAction_continuous π).const_smul (permutationSign π))
  exact hs.const_smul ((Fintype.card (Equiv.Perm (Fin N)) : ℂ)⁻¹)

/-- The full componentwise weak H2 domain is a submodule of finite-spin L2. -/
def spinH2Submodule (N : ℕ) : Submodule ℂ (SpinSpace N) where
  carrier := {ψ | ∀ σ, HasH2 (ψ σ)}
  zero_mem' := fun _ => hasH2_zero N
  add_mem' := fun hf hg σ => (hf σ).add (hg σ)
  smul_mem' := fun c _ hf σ => (hf σ).smul c

theorem spinAction_preserves_H2 {N : ℕ} (π : Equiv.Perm (Fin N))
    {ψ : SpinSpace N} (hψ : ∀ σ, HasH2 (ψ σ)) :
    ∀ σ, HasH2 (spinAction π ψ σ) :=
  fun σ => (hψ (permuteSpin π σ)).permute π

theorem fermionicProjection_preserves_H2 {N : ℕ} {ψ : SpinSpace N}
    (hψ : ∀ σ, HasH2 (ψ σ)) :
    ∀ σ, HasH2 (fermionicProjection N ψ σ) := by
  change fermionicProjection N ψ ∈ spinH2Submodule N
  rw [fermionicProjection_apply]
  apply (spinH2Submodule N).smul_mem
  apply (spinH2Submodule N).sum_mem
  intro π _
  exact (spinH2Submodule N).smul_mem _ (spinAction_preserves_H2 π hψ)

def fermionicProjectionToSpace (N : ℕ) : SpinSpace N → FermionicSpace N :=
  fun ψ => ⟨fermionicProjection N ψ, fermionicProjection_mem N ψ⟩

theorem fermionicProjectionToSpace_continuous (N : ℕ) :
    Continuous (fermionicProjectionToSpace N) :=
  (fermionicProjection_continuous N).subtype_mk _

theorem fermionicProjectionToSpace_surjective (N : ℕ) :
    Function.Surjective (fermionicProjectionToSpace N) := by
  intro ψ
  refine ⟨ψ.val, ?_⟩
  apply Subtype.ext
  exact fermionicProjection_id ψ.property

/-- The exact weak-H2 fermionic domain is dense in the actual fermionic Hilbert
space. This does not yet assert equality with the Coulomb operator's domain. -/
theorem fermionic_weakH2_dense (N : ℕ) :
    Dense {ψ : FermionicSpace N | ∀ σ, HasH2 (ψ.val σ)} := by
  apply (fermionicProjectionToSpace_surjective N).denseRange.dense_of_mapsTo
    (fermionicProjectionToSpace_continuous N) (weakH2_spin_dense_in_L2 N)
  intro ψ hψ
  exact fermionicProjection_preserves_H2 hψ

#print axioms fermionicProjection_apply
#print axioms fermionicProjection_mem
#print axioms fermionicProjection_id
#print axioms fermionicProjection_continuous
#print axioms fermionicProjection_preserves_H2
#print axioms fermionicProjectionToSpace_surjective
#print axioms fermionic_weakH2_dense
end TheoremT.Continuum
