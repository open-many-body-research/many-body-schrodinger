import ContinuumFoundation_v1

noncomputable section
open MeasureTheory
namespace TheoremT.Continuum

theorem fermionicSubspace_closed (N : ℕ) :
    IsClosed (fermionicSubspace N : Set (SpinSpace N)) := by
  change IsClosed {ψ : SpinSpace N | ∀ π σ,
    pullback π (ψ (permuteSpin π σ)) = permutationSign π • ψ σ}
  simp_rw [Set.ofPred_forall]
  apply isClosed_iInter
  intro π
  apply isClosed_iInter
  intro σ
  apply isClosed_eq
  · exact (Lp.compMeasurePreservingₗᵢ ℂ (permuteSpace π)
      (permuteSpace π).measurePreserving).continuous.comp
        (PiLp.continuous_apply 2 (fun _ : SpinConfiguration N => SpatialL2 N)
          (permuteSpin π σ))
  · exact (PiLp.continuous_apply 2 (fun _ : SpinConfiguration N => SpatialL2 N)
      σ).const_smul (permutationSign π)

instance fermionicCompleteSpace (N : ℕ) : CompleteSpace (FermionicSpace N) :=
  (fermionicSubspace_closed N).completeSpace_coe

#print axioms fermionicSubspace_closed
#synth InnerProductSpace ℂ (FermionicSpace 3)
#synth CompleteSpace (FermionicSpace 3)

end TheoremT.Continuum
