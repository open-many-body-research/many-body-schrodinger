import TwoElectronRelativeSobolev_v1
import HydrogenUncertainty_v1

/-! Sharp relative-coordinate Coulomb uncertainty on the actual weak H1 space.
No pointwise or weak differentiability at a collision is assumed. -/
noncomputable section
open MeasureTheory Filter
namespace TheoremT.Continuum

theorem twoElectronRelativeEquiv_involutive : Function.Involutive twoElectronRelativeEquiv :=
  twoElectronHadamard_involutive

theorem twoElectronRelative_pair_integral (f : SpatialL2 2) :
    (∫ q, ‖f q‖^2 / ‖position q 0 - position q 1‖) =
      (Real.sqrt 2)⁻¹ * ∫ q, ‖twoElectronRelativePull f q‖^2 / ‖position q 1‖ := by
  calc
    _ = ∫ q, ‖f (twoElectronRelativeEquiv q)‖^2 /
        ‖position (twoElectronRelativeEquiv q) 0 - position (twoElectronRelativeEquiv q) 1‖ :=
      (twoElectronRelativeEquiv_measurePreserving.integral_comp
        twoElectronRelativeEquiv.toHomeomorph.measurableEmbedding
        (fun q => ‖f q‖^2 / ‖position q 0 - position q 1‖)).symm
    _ = ∫ q, (Real.sqrt 2)⁻¹ * (‖twoElectronRelativePull f q‖^2 / ‖position q 1‖) := by
      apply integral_congr_ae
      filter_upwards [twoElectronRelativePull_ae f] with q hq
      simp only [Function.comp_apply] at hq
      rw [hq,twoElectronRelativeEquiv_pair_norm,twoElectronRelativeEquiv_involutive]
      ring
    _ = _ := integral_const_mul _ _

theorem twoElectronRelativeGradient_second_norm_sq (d : Coordinate 2 → SpatialL2 2)
    (k : Fin 3) :
    ‖twoElectronRelativeGradient d (1,k)‖^2 = (1/2 : ℝ) * ‖d (0,k) - d (1,k)‖^2 := by
  have h : twoElectronRelativeGradient d (1,k) =
      ((Real.sqrt 2)⁻¹ : ℂ) • twoElectronRelativePull (d (0,k) - d (1,k)) := by
    simp [twoElectronRelativeGradient,twoElectronRelativeSign,map_sub,sub_eq_add_neg]
  rw [h,norm_smul,mul_pow,twoElectronRelativePull.norm_map,norm_inv,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.sqrt_pos.mpr (by norm_num)),inv_pow,
    Real.sq_sqrt (by norm_num)]
  norm_num

theorem twoElectron_pair_coulomb_uncertainty_sq (f : SpatialL2 2)
    (d : Coordinate 2 → SpatialL2 2) (hd : ∀ k, WeakPartial f (d k) k) :
    (∫ q, ‖f q‖^2 / ‖position q 0 - position q 1‖)^2 ≤
      (1/4 : ℝ) * ‖f‖^2 * ∑ k : Fin 3, ‖d (0,k) - d (1,k)‖^2 := by
  let J : ℝ := ∫ q, ‖twoElectronRelativePull f q‖^2 / ‖position q 1‖
  let G : ℝ := ∑ k : Fin 3, ‖twoElectronRelativeGradient d (1,k)‖^2
  have hJ : 0 ≤ J := integral_nonneg (fun q => by positivity)
  have hG : 0 ≤ G := Finset.sum_nonneg (fun k _ => sq_nonneg _)
  have h := weak_nuclear_coulomb_uncertainty (1 : Fin 2)
    (twoElectronRelativePull f) (twoElectronRelativeGradient d) (twoElectronRelative_weakPartial f d hd)
  rw [twoElectronRelativePull.norm_map] at h
  change J ≤ ‖f‖ * Real.sqrt G at h
  have hsq : J^2 ≤ ‖f‖^2 * G := by
    have ht := (sq_le_sq₀ hJ (by positivity : 0 ≤ ‖f‖ * Real.sqrt G)).mpr h
    simpa only [mul_pow,Real.sq_sqrt hG] using ht
  rw [twoElectronRelative_pair_integral,mul_pow]
  change ((Real.sqrt 2)⁻¹)^2 * J^2 ≤ _
  calc
    _ ≤ ((Real.sqrt 2)⁻¹)^2 * (‖f‖^2 * G) :=
      mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
    _ = _ := by
      rw [inv_pow,Real.sq_sqrt (by norm_num)]
      simp only [G,twoElectronRelativeGradient_second_norm_sq,← Finset.mul_sum]
      ring

#print axioms twoElectronRelative_pair_integral
#print axioms twoElectronRelativeGradient_second_norm_sq
#print axioms twoElectron_pair_coulomb_uncertainty_sq
end TheoremT.Continuum
