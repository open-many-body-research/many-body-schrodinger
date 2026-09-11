import FermionicDensity_v2

/-! The actual antisymmetrizer acts continuously on the entire weak H¹ graph.
Derivative coordinates are permuted together with spatial and spin labels. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace TheoremT.Continuum

theorem weakPartial_finsetSum {N : ℕ} {ι : Type*} (s : Finset ι)
    (f g : ι → SpatialL2 N) (k : Coordinate N)
    (h : ∀ i ∈ s, WeakPartial (f i) (g i) k) :
    WeakPartial (∑ i ∈ s, f i) (∑ i ∈ s, g i) k := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using weakPartial_zero (N := N) k
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha,Finset.sum_insert ha]
    exact weakPartial_add (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

def fermionicDerivativeProjection (N : ℕ) (d : Coordinate N → SpinSpace N)
    (k : Coordinate N) : SpinSpace N :=
  (Fintype.card (Equiv.Perm (Fin N)) : ℂ)⁻¹ •
    ∑ π : Equiv.Perm (Fin N), permutationSign π •
      spinAction π (d ((coordinatePermutation π).symm k))

theorem fermionicDerivativeProjection_continuous (N : ℕ) :
    Continuous (fermionicDerivativeProjection N : (Coordinate N → SpinSpace N) →
      Coordinate N → SpinSpace N) := by
  apply continuous_pi
  intro k
  have hs : Continuous (fun d : Coordinate N → SpinSpace N =>
      ∑ π : Equiv.Perm (Fin N), permutationSign π •
        spinAction π (d ((coordinatePermutation π).symm k))) :=
    continuous_finsetSum Finset.univ (fun π _ =>
      ((spinAction_continuous π).comp (continuous_apply ((coordinatePermutation π).symm k))).const_smul
        (permutationSign π))
  exact hs.const_smul ((Fintype.card (Equiv.Perm (Fin N)) : ℂ)⁻¹)

/-- The genuine weak derivative of the projected state is the projection of the
whole derivative graph, with the coordinate indices correctly transformed. -/
theorem fermionicProjection_weakPartial {N : ℕ} {ψ : SpinSpace N}
    (d : Coordinate N → SpinSpace N) (hd : ∀ σ k, WeakPartial (ψ σ) (d k σ) k)
    (σ : SpinConfiguration N) (k : Coordinate N) :
    WeakPartial (fermionicProjection N ψ σ) (fermionicDerivativeProjection N d k σ) k := by
  have ht (π : Equiv.Perm (Fin N)) :
      WeakPartial (spinAction π ψ σ)
        (spinAction π (d ((coordinatePermutation π).symm k)) σ) k := by
    change WeakPartial (pullback π (ψ (permuteSpin π σ)))
      (pullback π (d ((coordinatePermutation π).symm k) (permuteSpin π σ))) k
    simpa only [Equiv.apply_symm_apply] using weakPartial_pullback π
      (hd (permuteSpin π σ) ((coordinatePermutation π).symm k))
  have hs := weakPartial_finsetSum Finset.univ
    (fun π : Equiv.Perm (Fin N) => permutationSign π • spinAction π ψ σ)
    (fun π : Equiv.Perm (Fin N) => permutationSign π •
      spinAction π (d ((coordinatePermutation π).symm k)) σ) k
    (fun π _ => weakPartial_smul (permutationSign π) (ht π))
  have hscaled := weakPartial_smul ((Fintype.card (Equiv.Perm (Fin N)) : ℂ)⁻¹) hs
  rw [fermionicProjection_apply]
  simpa only [fermionicDerivativeProjection,WithLp.ofLp_smul,Pi.smul_apply,
    WithLp.ofLp_sum,Finset.sum_apply] using hscaled

/-- On a fermionic weak H¹ state, uniqueness of actual weak derivatives makes
the induced derivative-graph projection the identity. -/
theorem fermionicDerivativeProjection_id {N : ℕ} {ψ : SpinSpace N}
    (hψ : ψ ∈ fermionicSubspace N) (d : Coordinate N → SpinSpace N)
    (hd : ∀ σ k, WeakPartial (ψ σ) (d k σ) k) : fermionicDerivativeProjection N d = d := by
  funext k
  apply (WithLp.ext_iff 2).mpr
  funext σ
  have hp := fermionicProjection_weakPartial d hd σ k
  rw [fermionicProjection_id hψ] at hp
  exact weakPartial_unique hp (hd σ k)

#print axioms fermionicDerivativeProjection_continuous
#print axioms fermionicProjection_weakPartial
#print axioms fermionicDerivativeProjection_id
end TheoremT.Continuum
