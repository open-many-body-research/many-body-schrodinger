import WeakPermutation_v2
import Mathlib.MeasureTheory.Measure.OpenPos

noncomputable section
open MeasureTheory Filter
namespace TheoremT.Continuum

theorem fermionic_continuous_representative_antisymmetric {N : ℕ}
    {ψ : SpinSpace N} (hψ : ψ ∈ fermionicSubspace N)
    {u : SpinConfiguration N → Configuration N → ℂ}
    (hu : ∀ σ, Continuous (u σ))
    (hEq : ∀ σ, (ψ σ : Configuration N → ℂ) =ᵐ[volume] u σ) :
    ∀ π : Equiv.Perm (Fin N), ∀ σ, ∀ x,
      u (permuteSpin π σ) (permuteSpace π x)=permutationSign π • u σ x := by
  intro π σ
  have he : (fun x => u (permuteSpin π σ) (permuteSpace π x)) =ᵐ[volume]
      (fun x => permutationSign π • u σ x) := by
    have hperm := hψ π σ
    have hp := pullback_ae π (ψ (permuteSpin π σ))
    rw [hperm] at hp
    filter_upwards [hp,Lp.coeFn_smul (permutationSign π) (ψ σ),hEq σ,
      (permuteSpace π).measurePreserving.quasiMeasurePreserving.ae (hEq (permuteSpin π σ))]
      with x hx hs he hpe
    change (permutationSign π • ψ σ) x = ψ (permuteSpin π σ) (permuteSpace π x) at hx
    rw [hs] at hx
    exact hpe.symm.trans (hx.symm.trans (congrArg (fun z => permutationSign π • z) he))
  exact congrFun (volume.eq_of_ae_eq he ((hu _).comp (permuteSpace π).continuous)
    (by fun_prop))

#print axioms fermionic_continuous_representative_antisymmetric
end TheoremT.Continuum
