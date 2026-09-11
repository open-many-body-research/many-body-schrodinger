import TwoElectronPairUncertainty_v1
import TwoElectronTensorH2_v1

/-! A certified repulsion upper bound for a normalized repeated product.
The nonnegative cross term improves the separate-electron uncertainty estimate. -/
noncomputable section
open MeasureTheory
namespace TheoremT.Continuum

theorem twoElectronTensor_exchange_cross (a f : SpatialL2 1) :
    (inner ℂ (twoElectronTensor a f) (twoElectronTensor f a)).re =
      ‖inner ℂ f a‖^2 := by
  rw [twoElectronTensor_inner,← inner_conj_symm a f]
  change (starRingEnd ℂ (inner ℂ f a) * inner ℂ f a).re = _
  rw [Complex.conj_mul']
  norm_cast

theorem twoElectronTensor_derivative_difference_norm (a f : SpatialL2 1) (hf : ‖f‖=1) :
    ‖twoElectronTensor a f - twoElectronTensor f a‖^2 ≤ 2 * ‖a‖^2 := by
  rw [norm_sub_sq (𝕜 := ℂ)]
  change ‖twoElectronTensor a f‖^2 - 2 *
    (inner ℂ (twoElectronTensor a f) (twoElectronTensor f a)).re + ‖twoElectronTensor f a‖^2 ≤ _
  rw [twoElectronTensor_exchange_cross,twoElectronTensor_norm,
    twoElectronTensor_norm,hf,mul_one,one_mul]
  nlinarith [sq_nonneg ‖inner ℂ f a‖]

theorem twoElectronTensor_pair_repulsion_sq (f : SpatialL2 1) (hf : ‖f‖=1)
    (d : Coordinate 1 → SpatialL2 1) (hd : ∀ k, WeakPartial f (d k) k) :
    (∫ q, ‖twoElectronTensor f f q‖^2 / ‖position q 0 - position q 1‖)^2 ≤
      (1/2 : ℝ) * ∑ k : Fin 3, ‖d (0,k)‖^2 := by
  have h := twoElectron_pair_coulomb_uncertainty_sq (twoElectronTensor f f)
    (twoElectronTensorGradient f f d d) (twoElectronTensorGradient_weak f f d d hd hd)
  have hg : (∑ k : Fin 3, ‖twoElectronTensorGradient f f d d (0,k) -
      twoElectronTensorGradient f f d d (1,k)‖^2) ≤ 2 * ∑ k : Fin 3, ‖d (0,k)‖^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    simpa [twoElectronTensorGradient] using twoElectronTensor_derivative_difference_norm (d (0,k)) f hf
  rw [twoElectronTensor_norm,hf] at h
  norm_num at h
  linarith

#print axioms twoElectronTensor_exchange_cross
#print axioms twoElectronTensor_derivative_difference_norm
#print axioms twoElectronTensor_pair_repulsion_sq
end TheoremT.Continuum
