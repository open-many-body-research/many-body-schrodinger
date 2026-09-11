import TwoElectronSecondSliceH1_v1
import TwoElectronPartialIntegral_v1

/-! Exact mass and partial-contraction normalization in physical slices. -/
noncomputable section
open MeasureTheory
namespace TheoremT.Continuum

theorem twoElectronFirstSlice_norm_sq_integrable (F : SpatialL2 2) :
    Integrable (fun y => ‖twoElectronFirstSlice F y‖ ^ 2) volume := by
  apply (ProductL2.sliceNormSq_integrable (twoElectronL2ProductEquiv F)).congr
  filter_upwards [ProductL2.sliceLeft_norm_sq_ae (twoElectronL2ProductEquiv F)] with y hy
  exact hy.symm

theorem twoElectronFirstSlice_norm_sq_integral (F : SpatialL2 2) :
    (∫ y, ‖twoElectronFirstSlice F y‖ ^ 2) = ‖F‖ ^ 2 := by
  calc
    _ = ∫ y, ProductL2.sliceNormSq (twoElectronL2ProductEquiv F) y :=
      integral_congr_ae (ProductL2.sliceLeft_norm_sq_ae (twoElectronL2ProductEquiv F))
    _ = ‖twoElectronL2ProductEquiv F‖ ^ 2 := ProductL2.sliceNormSq_integral _
    _ = ‖F‖ ^ 2 := by rw [twoElectronL2ProductEquiv.norm_map]

theorem pullback_norm_preserved {N : ℕ} (π : Equiv.Perm (Fin N)) (F : SpatialL2 N) :
    ‖pullback π F‖ = ‖F‖ :=
  (Lp.compMeasurePreservingₗᵢ ℂ (permuteSpace π) (permuteSpace π).measurePreserving).norm_map F

theorem twoElectronSecondSlice_norm_sq_integrable (F : SpatialL2 2) :
    Integrable (fun x => ‖twoElectronSecondSlice F x‖ ^ 2) volume :=
  twoElectronFirstSlice_norm_sq_integrable (pullback twoElectronSwap F)

theorem twoElectronSecondSlice_norm_sq_integral (F : SpatialL2 2) :
    (∫ x, ‖twoElectronSecondSlice F x‖ ^ 2) = ‖F‖ ^ 2 := by
  rw [show (fun x => ‖twoElectronSecondSlice F x‖ ^ 2) =
    (fun x => ‖twoElectronFirstSlice (pullback twoElectronSwap F) x‖ ^ 2) from rfl]
  rw [twoElectronFirstSlice_norm_sq_integral,pullback_norm_preserved]

theorem twoElectronFirstSlice_inner_contract_ae (f : SpatialL2 1) (F : SpatialL2 2) :
    (fun y => inner ℂ f (twoElectronFirstSlice F y)) =ᵐ[volume] twoElectronContractFirst f F := by
  filter_upwards [twoElectronFirstSlice_ae_of_ae F F (Filter.Eventually.of_forall (fun _ => rfl)),
    twoElectronContractFirst_ae_integral f F] with y hy hc
  rw [L2.inner_def,hc]
  apply integral_congr_ae
  filter_upwards [hy] with x hx
  rw [hx]

theorem twoElectronSecondSlice_inner_contract_ae (g : SpatialL2 1) (F : SpatialL2 2) :
    (fun x => inner ℂ g (twoElectronSecondSlice F x)) =ᵐ[volume] twoElectronContractSecond g F := by
  filter_upwards [twoElectronSecondSlice_ae_coe F,twoElectronContractSecond_ae_integral g F]
    with x hx hc
  rw [L2.inner_def,hc]
  apply integral_congr_ae
  filter_upwards [hx] with y hy
  rw [hy]

theorem twoElectronFirstSlice_amplitude_sq_integrable (f : SpatialL2 1) (F : SpatialL2 2) :
    Integrable (fun y => ‖inner ℂ f (twoElectronFirstSlice F y)‖ ^ 2) volume := by
  apply ((Lp.memLp (twoElectronContractFirst f F)).integrable_norm_pow
    (by norm_num : (2 : ℕ) ≠ 0)).congr
  filter_upwards [twoElectronFirstSlice_inner_contract_ae f F] with y hy
  rw [hy]

theorem twoElectronSecondSlice_amplitude_sq_integrable (g : SpatialL2 1) (F : SpatialL2 2) :
    Integrable (fun x => ‖inner ℂ g (twoElectronSecondSlice F x)‖ ^ 2) volume := by
  apply ((Lp.memLp (twoElectronContractSecond g F)).integrable_norm_pow
    (by norm_num : (2 : ℕ) ≠ 0)).congr
  filter_upwards [twoElectronSecondSlice_inner_contract_ae g F] with x hx
  rw [hx]

theorem twoElectronFirstSlice_amplitude_sq_integral (f : SpatialL2 1) (hf : ‖f‖=1)
    (F : SpatialL2 2) : (∫ y, ‖inner ℂ f (twoElectronFirstSlice F y)‖ ^ 2) =
      ‖twoElectronProjectFirst f F‖ ^ 2 := by
  rw [twoElectronProjectFirst_apply,twoElectronTensor_norm,hf,one_mul,ProductL2.norm_sq_integral]
  exact integral_congr_ae
    ((twoElectronFirstSlice_inner_contract_ae f F).fun_comp (fun z : ℂ => ‖z‖ ^ 2))

theorem twoElectronSecondSlice_amplitude_sq_integral (g : SpatialL2 1) (hg : ‖g‖=1)
    (F : SpatialL2 2) : (∫ x, ‖inner ℂ g (twoElectronSecondSlice F x)‖ ^ 2) =
      ‖twoElectronProjectSecond g F‖ ^ 2 := by
  rw [twoElectronProjectSecond_apply,twoElectronTensor_norm,hg,mul_one,ProductL2.norm_sq_integral]
  exact integral_congr_ae
    ((twoElectronSecondSlice_inner_contract_ae g F).fun_comp (fun z : ℂ => ‖z‖ ^ 2))

#print axioms twoElectronFirstSlice_norm_sq_integral
#print axioms twoElectronSecondSlice_norm_sq_integral
#print axioms twoElectronFirstSlice_amplitude_sq_integral
#print axioms twoElectronSecondSlice_amplitude_sq_integral
end TheoremT.Continuum
