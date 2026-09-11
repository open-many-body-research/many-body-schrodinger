import WeakPermutation_v2
import Mathlib.RepresentationTheory.Invariants

/-! The genuine simultaneous spatial/spin action and signed representation. -/
noncomputable section
open MeasureTheory Filter
namespace TheoremT.Continuum

theorem permutationSign_one (N : ℕ) : permutationSign (1 : Equiv.Perm (Fin N)) = 1 := by
  simp [permutationSign]

theorem permutationSign_mul {N : ℕ} (π τ : Equiv.Perm (Fin N)) :
    permutationSign (π * τ) = permutationSign π * permutationSign τ := by
  simp [permutationSign, map_mul]

theorem permutationSign_sq {N : ℕ} (π : Equiv.Perm (Fin N)) :
    permutationSign π * permutationSign π = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [permutationSign, h]

theorem pullback_one (N : ℕ) (f : SpatialL2 N) :
    pullback (1 : Equiv.Perm (Fin N)) f = f := by
  apply Lp.ext
  filter_upwards [pullback_ae 1 f] with x hx
  have hp : permuteSpace (1 : Equiv.Perm (Fin N)) x = x := by
    apply (WithLp.ext_iff 2).mpr
    funext k
    rfl
  simpa only [Function.comp_apply, hp] using hx

theorem pullback_mul {N : ℕ} (π τ : Equiv.Perm (Fin N)) (f : SpatialL2 N) :
    pullback (π * τ) f = pullback π (pullback τ f) := by
  apply Lp.ext
  have hcomp := (permuteSpace π).measurePreserving.quasiMeasurePreserving.ae (pullback_ae τ f)
  filter_upwards [pullback_ae (π * τ) f, pullback_ae π (pullback τ f), hcomp]
    with x hleft hright hcomp
  simp only [Function.comp_apply] at hleft hright hcomp
  rw [hleft, hright, hcomp]
  rfl

def spinAction {N : ℕ} (π : Equiv.Perm (Fin N)) : SpinSpace N →ₗ[ℂ] SpinSpace N where
  toFun ψ := WithLp.toLp 2 (fun σ => pullback π (ψ (permuteSpin π σ)))
  map_add' ψ φ := by
    apply (WithLp.ext_iff 2).mpr
    funext σ
    exact map_add (pullback π) _ _
  map_smul' c ψ := by
    apply (WithLp.ext_iff 2).mpr
    funext σ
    exact map_smul (pullback π) c _

theorem spinAction_one (N : ℕ) (ψ : SpinSpace N) :
    spinAction (1 : Equiv.Perm (Fin N)) ψ = ψ := by
  apply (WithLp.ext_iff 2).mpr
  funext σ
  exact pullback_one N (ψ σ)

theorem spinAction_mul {N : ℕ} (π τ : Equiv.Perm (Fin N)) (ψ : SpinSpace N) :
    spinAction (π * τ) ψ = spinAction π (spinAction τ ψ) := by
  apply (WithLp.ext_iff 2).mpr
  funext σ
  exact pullback_mul π τ _

theorem spinAction_continuous {N : ℕ} (π : Equiv.Perm (Fin N)) :
    Continuous (spinAction π : SpinSpace N → SpinSpace N) := by
  apply (PiLp.continuousLinearEquiv 2 ℂ (fun _ : SpinConfiguration N => SpatialL2 N)).symm.continuous.comp
  apply continuous_pi
  intro σ
  exact (Lp.compMeasurePreservingₗᵢ ℂ (permuteSpace π)
    (permuteSpace π).measurePreserving).continuous.comp
    (PiLp.continuous_apply 2 (fun _ : SpinConfiguration N => SpatialL2 N) (permuteSpin π σ))

/-- The sign-twisted representation has the fermionic states as fixed vectors. -/
def signedSpinRepresentation (N : ℕ) :
    Representation ℂ (Equiv.Perm (Fin N)) (SpinSpace N) where
  toFun π := permutationSign π • spinAction π
  map_one' := by
    apply LinearMap.ext
    intro ψ
    simp only [LinearMap.smul_apply, permutationSign_one, one_smul,
      spinAction_one, Module.End.one_apply]
  map_mul' π τ := by
    apply LinearMap.ext
    intro ψ
    simp only [LinearMap.smul_apply, Module.End.mul_apply,
      map_smul, permutationSign_mul, spinAction_mul, smul_smul]
    rw [mul_comm]

theorem signedSpinRepresentation_invariants (N : ℕ) :
    (signedSpinRepresentation N).invariants = fermionicSubspace N := by
  apply Submodule.ext
  intro ψ
  constructor
  · intro h π σ
    have hx := congrArg (fun χ : SpinSpace N => χ σ) (h π)
    change permutationSign π • pullback π (ψ (permuteSpin π σ)) = ψ σ at hx
    have hs := congrArg (fun v : SpatialL2 N => permutationSign π • v) hx
    simpa only [smul_smul, permutationSign_sq, one_smul] using hs
  · intro h π
    apply (WithLp.ext_iff 2).mpr
    funext σ
    change permutationSign π • pullback π (ψ (permuteSpin π σ)) = ψ σ
    rw [h π σ, smul_smul, permutationSign_sq, one_smul]

#print axioms pullback_mul
#print axioms spinAction_mul
#print axioms spinAction_continuous
#print axioms signedSpinRepresentation_invariants
end TheoremT.Continuum
