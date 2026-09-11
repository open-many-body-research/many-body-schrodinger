import HardyFreeGraph_v1

/-! Covariance of the actual shifted free graph and fermionic inverse images,
proved from uniqueness rather than assuming Fourier covariance. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace TheoremT.Continuum

theorem positiveFreeGraph_pullback {N : ℕ} {μ : ℝ} (π : Equiv.Perm (Fin N))
    {u f : SpatialL2 N} (h : positiveFreeGraph μ u f) :
    positiveFreeGraph μ (pullback π u) (pullback π f) := by
  obtain ⟨d,e,hd,he,hout⟩ := h
  let c := coordinatePermutation π
  refine ⟨fun k => pullback π (d (c.symm k)),
    fun k l => pullback π (e (c.symm k) (c.symm l)), ?_, ?_, ?_⟩
  · intro k
    simpa only [c,Equiv.apply_symm_apply] using weakPartial_pullback π (hd (c.symm k))
  · intro k l
    simpa only [c,Equiv.apply_symm_apply] using weakPartial_pullback π
      (he (c.symm k) (c.symm l))
  · rw [hout,map_add,LinearMap.map_smul_of_tower,LinearMap.map_smul_of_tower,map_sum]
    rw [Equiv.sum_comp c.symm (fun k => pullback π (e k k))]

/-- The inverse image of a fermionic source under a positive free shift is
fermionic; every scalar output is identified by the proved coercive uniqueness. -/
theorem positiveFreeGraph_solutions_fermionic {N : ℕ} {μ : ℝ} (hμ : 0 < μ)
    {u f : SpinSpace N} (hf : f ∈ fermionicSubspace N)
    (hu : ∀ σ, positiveFreeGraph μ (u σ) (f σ)) : u ∈ fermionicSubspace N := by
  intro π σ
  have hleft := positiveFreeGraph_pullback π (hu (permuteSpin π σ))
  rw [hf π σ] at hleft
  exact positiveFreeGraph_input_unique hμ hleft
    (positiveFreeGraph_smul (permutationSign π) (hu σ))

/-- Any everywhere-defined scalar right inverse commutes with coordinate
permutations, as a consequence of actual free-graph uniqueness. -/
theorem positiveFree_inverse_pullback {N : ℕ} {μ : ℝ} (hμ : 0 < μ)
    (R : SpatialL2 N → SpatialL2 N) (hR : ∀ f, positiveFreeGraph μ (R f) f)
    (π : Equiv.Perm (Fin N)) (f : SpatialL2 N) :
    R (pullback π f) = pullback π (R f) :=
  positiveFreeGraph_input_unique hμ (hR _) (positiveFreeGraph_pullback π (hR f))

#print axioms positiveFreeGraph_pullback
#print axioms positiveFreeGraph_solutions_fermionic
#print axioms positiveFree_inverse_pullback
end TheoremT.Continuum
