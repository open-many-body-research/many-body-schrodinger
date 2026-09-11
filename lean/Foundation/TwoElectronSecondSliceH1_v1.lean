import TwoElectronFirstSliceH1_v1
import TwoElectronTensorExchange_v1

/-! The other physical electron slice, using the proved actual exchange covariance. -/
noncomputable section
open MeasureTheory
namespace TheoremT.Continuum

def twoElectronSecondSlice (F : SpatialL2 2) (x : Configuration 1) : SpatialL2 1 :=
  twoElectronFirstSlice (pullback twoElectronSwap F) x

theorem twoElectron_reassemble_swap (x y : Configuration 1) :
    permuteSpace twoElectronSwap (twoElectronConfigurationProduct.symm (x,y)) =
      twoElectronConfigurationProduct.symm (y,x) := by
  apply twoElectronConfigurationProduct.injective
  rw [twoElectronConfigurationProduct_swap]
  simp

theorem twoElectronSecondSlice_ae_coe (F : SpatialL2 2) :
    ∀ᵐ x ∂volume, twoElectronSecondSlice F x =ᵐ[volume]
      fun y => F (twoElectronConfigurationProduct.symm (x,y)) := by
  have h := twoElectronFirstSlice_ae_of_ae (pullback twoElectronSwap F)
    (F ∘ permuteSpace twoElectronSwap) (pullback_ae twoElectronSwap F)
  filter_upwards [h] with x hx
  simpa only [twoElectronSecondSlice,Function.comp_apply,twoElectron_reassemble_swap] using hx

theorem twoElectronSecondSlice_weakPartial_ae (F : SpatialL2 2)
    (d : Coordinate 2 → SpatialL2 2) (hd : ∀ k, WeakPartial F (d k) k) :
    ∀ᵐ x ∂volume, ∀ k : Fin 3,
      WeakPartial (twoElectronSecondSlice F x) (twoElectronSecondSlice (d (1,k)) x) (0,k) := by
  let dp : Coordinate 2 → SpatialL2 2 :=
    fun k => pullback twoElectronSwap (d ((coordinatePermutation twoElectronSwap).symm k))
  have hp : ∀ k, WeakPartial (pullback twoElectronSwap F) (dp k) k := by
    intro k
    simpa only [Equiv.apply_symm_apply] using
      weakPartial_pullback twoElectronSwap (hd ((coordinatePermutation twoElectronSwap).symm k))
  filter_upwards [twoElectronFirstSlice_weakPartial_ae (pullback twoElectronSwap F) dp hp] with x hx
  intro k
  have h := hx k
  simpa [dp,twoElectronSecondSlice,coordinatePermutation,twoElectronSwap] using h

theorem twoElectronSecondSlice_hasH1_ae (F : SpatialL2 2) (hF : HasH1 F) :
    ∀ᵐ x ∂volume, HasH1 (twoElectronSecondSlice F x) :=
  twoElectronFirstSlice_hasH1_ae _ (hF.permute twoElectronSwap)

#print axioms twoElectronSecondSlice_ae_coe
#print axioms twoElectronSecondSlice_weakPartial_ae
#print axioms twoElectronSecondSlice_hasH1_ae
end TheoremT.Continuum
