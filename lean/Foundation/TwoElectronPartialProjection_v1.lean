import TwoElectronCoordinateProduct_v1
import ProductL2Projection_v1

/-! Partial contractions and projections on the actual scalar two-electron L2.
These are Hilbert adjoints of literal coordinate product-function embeddings.
They are mathematical bounded linear maps, not executable integration routines.
No individual map is asserted to preserve the fermionic subspace. -/
noncomputable section
open MeasureTheory
namespace TheoremT.Continuum

def twoElectronTensor (f g : SpatialL2 1) : SpatialL2 2 :=
  twoElectronL2ProductEquiv.symm (ProductL2.tensor f g)

theorem twoElectronTensor_toProduct (f g : SpatialL2 1) :
    twoElectronL2ProductEquiv (twoElectronTensor f g) = ProductL2.tensor f g :=
  twoElectronL2ProductEquiv.apply_symm_apply _

theorem twoElectronTensor_ae (f g : SpatialL2 1) :
    twoElectronTensor f g =ᵐ[volume]
      fun x => f (twoElectronConfigurationProduct x).1 *
        g (twoElectronConfigurationProduct x).2 := by
  filter_upwards [twoElectronL2Pullback_ae (ProductL2.tensor f g),
    twoElectronConfigurationProduct_measurePreserving.quasiMeasurePreserving.ae
      (ProductL2.tensor_ae f g)] with x hx hprod
  exact hx.trans hprod

theorem twoElectronTensor_norm (f g : SpatialL2 1) :
    ‖twoElectronTensor f g‖ = ‖f‖ * ‖g‖ := by
  rw [twoElectronTensor, twoElectronL2ProductEquiv.symm.norm_map, ProductL2.tensor_norm]

theorem twoElectronTensor_inner (f h g k : SpatialL2 1) :
    inner ℂ (twoElectronTensor f g) (twoElectronTensor h k) =
      inner ℂ f h * inner ℂ g k := by
  rw [twoElectronTensor,twoElectronTensor,
    twoElectronL2ProductEquiv.symm.inner_map_map, ProductL2.tensor_inner]

def twoElectronContractFirst (f : SpatialL2 1) : SpatialL2 2 →L[ℂ] SpatialL2 1 :=
  (ProductL2.contractLeft f).comp twoElectronL2ProductEquiv.toLinearIsometry.toContinuousLinearMap

def twoElectronContractSecond (g : SpatialL2 1) : SpatialL2 2 →L[ℂ] SpatialL2 1 :=
  (ProductL2.contractRight g).comp twoElectronL2ProductEquiv.toLinearIsometry.toContinuousLinearMap

theorem twoElectronContractFirst_norm (f : SpatialL2 1) (F : SpatialL2 2) :
    ‖twoElectronContractFirst f F‖ ≤ ‖f‖ * ‖F‖ := by
  simpa [twoElectronContractFirst] using
    ProductL2.contractLeft_norm_bound f (twoElectronL2ProductEquiv F)

theorem twoElectronContractSecond_norm (g : SpatialL2 1) (F : SpatialL2 2) :
    ‖twoElectronContractSecond g F‖ ≤ ‖g‖ * ‖F‖ := by
  simpa [twoElectronContractSecond] using
    ProductL2.contractRight_norm_bound g (twoElectronL2ProductEquiv F)

theorem twoElectronContractFirst_pairing (f g : SpatialL2 1) (F : SpatialL2 2) :
    inner ℂ g (twoElectronContractFirst f F) = inner ℂ (twoElectronTensor f g) F := by
  change inner ℂ g (ProductL2.contractLeft f (twoElectronL2ProductEquiv F)) = _
  rw [ProductL2.contractLeft_pairing,
    ← twoElectronL2ProductEquiv.inner_map_map (twoElectronTensor f g) F,
    twoElectronTensor_toProduct]

theorem twoElectronContractSecond_pairing (f g : SpatialL2 1) (F : SpatialL2 2) :
    inner ℂ f (twoElectronContractSecond g F) = inner ℂ (twoElectronTensor f g) F := by
  change inner ℂ f (ProductL2.contractRight g (twoElectronL2ProductEquiv F)) = _
  rw [ProductL2.contractRight_pairing,
    ← twoElectronL2ProductEquiv.inner_map_map (twoElectronTensor f g) F,
    twoElectronTensor_toProduct]

def twoElectronProjectFirst (f : SpatialL2 1) : SpatialL2 2 →L[ℂ] SpatialL2 2 :=
  twoElectronL2ProductEquiv.symm.toLinearIsometry.toContinuousLinearMap.comp
    ((ProductL2.projectLeft f).comp twoElectronL2ProductEquiv.toLinearIsometry.toContinuousLinearMap)

def twoElectronProjectSecond (g : SpatialL2 1) : SpatialL2 2 →L[ℂ] SpatialL2 2 :=
  twoElectronL2ProductEquiv.symm.toLinearIsometry.toContinuousLinearMap.comp
    ((ProductL2.projectRight g).comp twoElectronL2ProductEquiv.toLinearIsometry.toContinuousLinearMap)

theorem twoElectronProjectFirst_toProduct (f : SpatialL2 1) (F : SpatialL2 2) :
    twoElectronL2ProductEquiv (twoElectronProjectFirst f F) =
      ProductL2.projectLeft f (twoElectronL2ProductEquiv F) :=
  twoElectronL2ProductEquiv.apply_symm_apply _

theorem twoElectronProjectSecond_toProduct (g : SpatialL2 1) (F : SpatialL2 2) :
    twoElectronL2ProductEquiv (twoElectronProjectSecond g F) =
      ProductL2.projectRight g (twoElectronL2ProductEquiv F) :=
  twoElectronL2ProductEquiv.apply_symm_apply _

theorem twoElectronProjectFirst_apply (f : SpatialL2 1) (F : SpatialL2 2) :
    twoElectronProjectFirst f F = twoElectronTensor f (twoElectronContractFirst f F) := rfl

theorem twoElectronProjectSecond_apply (g : SpatialL2 1) (F : SpatialL2 2) :
    twoElectronProjectSecond g F = twoElectronTensor (twoElectronContractSecond g F) g := rfl

theorem twoElectronProjectFirst_idempotent (f : SpatialL2 1) (hf : ‖f‖ = 1)
    (F : SpatialL2 2) : twoElectronProjectFirst f (twoElectronProjectFirst f F) =
      twoElectronProjectFirst f F := by
  apply twoElectronL2ProductEquiv.injective
  simp only [twoElectronProjectFirst_toProduct]
  exact ProductL2.projectLeft_idempotent f hf _

theorem twoElectronProjectSecond_idempotent (g : SpatialL2 1) (hg : ‖g‖ = 1)
    (F : SpatialL2 2) : twoElectronProjectSecond g (twoElectronProjectSecond g F) =
      twoElectronProjectSecond g F := by
  apply twoElectronL2ProductEquiv.injective
  simp only [twoElectronProjectSecond_toProduct]
  exact ProductL2.projectRight_idempotent g hg _

theorem twoElectronProjectFirst_symmetric (f : SpatialL2 1) :
    (twoElectronProjectFirst f).toLinearMap.IsSymmetric := by
  intro F G
  change inner ℂ (twoElectronProjectFirst f F) G = inner ℂ F (twoElectronProjectFirst f G)
  rw [← twoElectronL2ProductEquiv.inner_map_map,
    ← twoElectronL2ProductEquiv.inner_map_map F,
    twoElectronProjectFirst_toProduct,twoElectronProjectFirst_toProduct]
  exact ProductL2.projectLeft_symmetric f _ _

theorem twoElectronProjectSecond_symmetric (g : SpatialL2 1) :
    (twoElectronProjectSecond g).toLinearMap.IsSymmetric := by
  intro F G
  change inner ℂ (twoElectronProjectSecond g F) G = inner ℂ F (twoElectronProjectSecond g G)
  rw [← twoElectronL2ProductEquiv.inner_map_map,
    ← twoElectronL2ProductEquiv.inner_map_map F,
    twoElectronProjectSecond_toProduct,twoElectronProjectSecond_toProduct]
  exact ProductL2.projectRight_symmetric g _ _

theorem twoElectronProjectFirst_isSymmetricProjection (f : SpatialL2 1) (hf : ‖f‖ = 1) :
    (twoElectronProjectFirst f).toLinearMap.IsSymmetricProjection := by
  constructor
  · apply LinearMap.ext
    exact twoElectronProjectFirst_idempotent f hf
  · exact twoElectronProjectFirst_symmetric f

theorem twoElectronProjectSecond_isSymmetricProjection (g : SpatialL2 1) (hg : ‖g‖ = 1) :
    (twoElectronProjectSecond g).toLinearMap.IsSymmetricProjection := by
  constructor
  · apply LinearMap.ext
    exact twoElectronProjectSecond_idempotent g hg
  · exact twoElectronProjectSecond_symmetric g

theorem twoElectronProjectFirstSecond (f g : SpatialL2 1) (F : SpatialL2 2) :
    twoElectronProjectFirst f (twoElectronProjectSecond g F) =
      inner ℂ (twoElectronTensor f g) F • twoElectronTensor f g := by
  apply twoElectronL2ProductEquiv.injective
  rw [twoElectronProjectFirst_toProduct,twoElectronProjectSecond_toProduct,
    ProductL2.projectLeft_projectRight, map_smul, twoElectronTensor_toProduct,
    ← twoElectronL2ProductEquiv.inner_map_map (twoElectronTensor f g) F,
    twoElectronTensor_toProduct]

theorem twoElectronProjectSecondFirst (f g : SpatialL2 1) (F : SpatialL2 2) :
    twoElectronProjectSecond g (twoElectronProjectFirst f F) =
      inner ℂ (twoElectronTensor f g) F • twoElectronTensor f g := by
  apply twoElectronL2ProductEquiv.injective
  rw [twoElectronProjectSecond_toProduct,twoElectronProjectFirst_toProduct,
    ProductL2.projectRight_projectLeft, map_smul, twoElectronTensor_toProduct,
    ← twoElectronL2ProductEquiv.inner_map_map (twoElectronTensor f g) F,
    twoElectronTensor_toProduct]

theorem twoElectronProject_commute (f g : SpatialL2 1) :
    Commute (twoElectronProjectFirst f).toLinearMap (twoElectronProjectSecond g).toLinearMap := by
  apply LinearMap.ext
  intro F
  exact (twoElectronProjectFirstSecond f g F).trans (twoElectronProjectSecondFirst f g F).symm

#print axioms twoElectronTensor_ae
#print axioms twoElectronContractFirst_norm
#print axioms twoElectronContractFirst_pairing
#print axioms twoElectronProjectFirst_isSymmetricProjection
#print axioms twoElectronProjectSecond_isSymmetricProjection
#print axioms twoElectronProjectFirstSecond
#print axioms twoElectronProject_commute
end TheoremT.Continuum
