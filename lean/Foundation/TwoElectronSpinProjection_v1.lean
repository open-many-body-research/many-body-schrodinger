import TwoElectronProjectionComparison_v1
import HardyFreeSpinLift_v1

/-! Actual ambient full-spin coordinate projections, by the existing bounded scalar spin lift.
No individual projection is restricted to the fermionic space. -/
noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum

theorem scalarSpinLift_symmetric {N : ℕ} (R : SpatialL2 N →L[ℂ] SpatialL2 N)
    (hR : R.toLinearMap.IsSymmetric) : (scalarSpinLift R).toLinearMap.IsSymmetric := by
  intro ψ χ
  change inner ℂ (scalarSpinLift R ψ) χ = inner ℂ ψ (scalarSpinLift R χ)
  simp only [PiLp.inner_apply,scalarSpinLift_apply]
  apply Finset.sum_congr rfl
  intro σ _
  exact hR (ψ σ) (χ σ)

theorem scalarSpinLift_idempotent {N : ℕ} (R : SpatialL2 N →L[ℂ] SpatialL2 N)
    (hR : ∀ f, R (R f) = R f) (ψ : SpinSpace N) :
    scalarSpinLift R (scalarSpinLift R ψ) = scalarSpinLift R ψ := by
  apply (WithLp.ext_iff 2).mpr
  funext σ
  exact hR (ψ σ)

theorem scalarSpinLift_isSymmetricProjection {N : ℕ}
    (R : SpatialL2 N →L[ℂ] SpatialL2 N) (hR : R.toLinearMap.IsSymmetricProjection) :
    (scalarSpinLift R).toLinearMap.IsSymmetricProjection := by
  constructor
  · apply LinearMap.ext
    apply scalarSpinLift_idempotent R
    intro f
    have h := congrArg (fun T : SpatialL2 N →ₗ[ℂ] SpatialL2 N => T f) hR.isIdempotentElem
    exact h
  · exact scalarSpinLift_symmetric R hR.isSymmetric

theorem scalarSpinLift_commute {N : ℕ} (R S : SpatialL2 N →L[ℂ] SpatialL2 N)
    (hRS : Commute R.toLinearMap S.toLinearMap) :
    Commute (scalarSpinLift R).toLinearMap (scalarSpinLift S).toLinearMap := by
  apply LinearMap.ext
  intro ψ
  apply (WithLp.ext_iff 2).mpr
  funext σ
  exact congrArg (fun T : SpatialL2 N →ₗ[ℂ] SpatialL2 N => T (ψ σ)) hRS.eq

def twoElectronSpinProjectFirst (f : SpatialL2 1) : SpinSpace 2 →L[ℂ] SpinSpace 2 :=
  scalarSpinLift (twoElectronProjectFirst f)

def twoElectronSpinProjectSecond (g : SpatialL2 1) : SpinSpace 2 →L[ℂ] SpinSpace 2 :=
  scalarSpinLift (twoElectronProjectSecond g)

theorem twoElectronSpinProjectFirst_apply (f : SpatialL2 1) (ψ : SpinSpace 2)
    (σ : SpinConfiguration 2) :
    twoElectronSpinProjectFirst f ψ σ = twoElectronProjectFirst f (ψ σ) := rfl

theorem twoElectronSpinProjectSecond_apply (g : SpatialL2 1) (ψ : SpinSpace 2)
    (σ : SpinConfiguration 2) :
    twoElectronSpinProjectSecond g ψ σ = twoElectronProjectSecond g (ψ σ) := rfl

theorem twoElectronSpinProjectFirst_isSymmetricProjection (f : SpatialL2 1) (hf : ‖f‖=1) :
    (twoElectronSpinProjectFirst f).toLinearMap.IsSymmetricProjection :=
  scalarSpinLift_isSymmetricProjection _ (twoElectronProjectFirst_isSymmetricProjection f hf)

theorem twoElectronSpinProjectSecond_isSymmetricProjection (g : SpatialL2 1) (hg : ‖g‖=1) :
    (twoElectronSpinProjectSecond g).toLinearMap.IsSymmetricProjection :=
  scalarSpinLift_isSymmetricProjection _ (twoElectronProjectSecond_isSymmetricProjection g hg)

theorem twoElectronSpinProject_commute (f g : SpatialL2 1) :
    Commute (twoElectronSpinProjectFirst f).toLinearMap
      (twoElectronSpinProjectSecond g).toLinearMap :=
  scalarSpinLift_commute _ _ (twoElectronProject_commute f g)

theorem twoElectronSpinProjectFirstSecond_apply (f g : SpatialL2 1) (ψ : SpinSpace 2)
    (σ : SpinConfiguration 2) :
    twoElectronSpinProjectFirst f (twoElectronSpinProjectSecond g ψ) σ =
      inner ℂ (twoElectronTensor f g) (ψ σ) • twoElectronTensor f g :=
  twoElectronProjectFirstSecond f g (ψ σ)

theorem twoElectronSpin_jointProjection_norm_sq (f g : SpatialL2 1)
    (hf : ‖f‖=1) (hg : ‖g‖=1) (ψ : SpinSpace 2) :
    ‖twoElectronSpinProjectFirst f (twoElectronSpinProjectSecond g ψ)‖ ^ 2 =
      ∑ σ : SpinConfiguration 2, ‖inner ℂ (twoElectronTensor f g) (ψ σ)‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro σ _
  exact twoElectron_jointProjection_norm_sq f g hf hg (ψ σ)

theorem twoElectronSpin_projection_norm_sum (f g : SpatialL2 1)
    (hf : ‖f‖=1) (hg : ‖g‖=1) (ψ : SpinSpace 2) :
    ‖twoElectronSpinProjectFirst f ψ‖ ^ 2 + ‖twoElectronSpinProjectSecond g ψ‖ ^ 2 ≤
      ‖ψ‖ ^ 2 + ∑ σ : SpinConfiguration 2, ‖inner ℂ (twoElectronTensor f g) (ψ σ)‖ ^ 2 := by
  have h := OperatorTheory.commuting_projections_norm_square
    (twoElectronSpinProjectFirst f).toLinearMap (twoElectronSpinProjectSecond g).toLinearMap
    (twoElectronSpinProjectFirst_isSymmetricProjection f hf)
    (twoElectronSpinProjectSecond_isSymmetricProjection g hg)
    (twoElectronSpinProject_commute f g) ψ
  change ‖twoElectronSpinProjectFirst f ψ‖ ^ 2 + ‖twoElectronSpinProjectSecond g ψ‖ ^ 2 ≤
    ‖ψ‖ ^ 2 + ‖twoElectronSpinProjectFirst f (twoElectronSpinProjectSecond g ψ)‖ ^ 2 at h
  rwa [twoElectronSpin_jointProjection_norm_sq f g hf hg ψ] at h

#print axioms scalarSpinLift_isSymmetricProjection
#print axioms twoElectronSpinProjectFirst_isSymmetricProjection
#print axioms twoElectronSpinProject_commute
#print axioms twoElectronSpinProjectFirstSecond_apply
#print axioms twoElectronSpin_projection_norm_sum
end TheoremT.Continuum
