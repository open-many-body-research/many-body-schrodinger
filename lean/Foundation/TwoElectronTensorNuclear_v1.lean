import TwoElectronTensorH2_v1
import HydrogenRadialTrace_v1

/-! Literal product nuclear expectations on the full physical measure. -/
noncomputable section
open MeasureTheory Filter
namespace TheoremT.Continuum

theorem twoElectronTensor_nuclear_first (f g : SpatialL2 1) :
    (∫ q, ‖twoElectronTensor f g q‖^2 / ‖position q 0‖) =
      (∫ x, ‖f x‖^2 / ‖position x 0‖) * ‖g‖^2 := by
  have he := twoElectronConfigurationProduct_symm_measurePreserving.quasiMeasurePreserving.ae
    (twoElectronTensor_ae f g)
  calc
    _ = ∫ p : Configuration 1 × Configuration 1,
        ‖twoElectronTensor f g (twoElectronConfigurationProduct.symm p)‖^2 /
          ‖position (twoElectronConfigurationProduct.symm p) 0‖
        ∂(volume : Measure (Configuration 1)).prod volume :=
      (twoElectronConfigurationProduct_symm_measurePreserving.integral_comp
        twoElectronConfigurationProduct.symm.toHomeomorph.measurableEmbedding
        (fun q => ‖twoElectronTensor f g q‖^2 / ‖position q 0‖)).symm
    _ = ∫ p : Configuration 1 × Configuration 1,
        (‖f p.1‖^2 / ‖position p.1 0‖) * ‖g p.2‖^2
        ∂(volume : Measure (Configuration 1)).prod volume := by
      apply integral_congr_ae
      filter_upwards [he] with p hp
      simp only [twoElectronConfigurationProduct.apply_symm_apply] at hp
      rw [hp,← twoElectronConfigurationProduct_fst_position,
        twoElectronConfigurationProduct.apply_symm_apply,norm_mul,mul_pow]
      ring
    _ = _ := by
      rw [integral_prod_mul (fun x : Configuration 1 => ‖f x‖^2 / ‖position x 0‖)
        (fun y : Configuration 1 => ‖g y‖^2),← ProductL2.norm_sq_integral]

theorem twoElectronTensor_nuclear_second (f g : SpatialL2 1) :
    (∫ q, ‖twoElectronTensor f g q‖^2 / ‖position q 1‖) =
      ‖f‖^2 * (∫ y, ‖g y‖^2 / ‖position y 0‖) := by
  have he := twoElectronConfigurationProduct_symm_measurePreserving.quasiMeasurePreserving.ae
    (twoElectronTensor_ae f g)
  calc
    _ = ∫ p : Configuration 1 × Configuration 1,
        ‖twoElectronTensor f g (twoElectronConfigurationProduct.symm p)‖^2 /
          ‖position (twoElectronConfigurationProduct.symm p) 1‖
        ∂(volume : Measure (Configuration 1)).prod volume :=
      (twoElectronConfigurationProduct_symm_measurePreserving.integral_comp
        twoElectronConfigurationProduct.symm.toHomeomorph.measurableEmbedding
        (fun q => ‖twoElectronTensor f g q‖^2 / ‖position q 1‖)).symm
    _ = ∫ p : Configuration 1 × Configuration 1,
        ‖f p.1‖^2 * (‖g p.2‖^2 / ‖position p.2 0‖)
        ∂(volume : Measure (Configuration 1)).prod volume := by
      apply integral_congr_ae
      filter_upwards [he] with p hp
      simp only [twoElectronConfigurationProduct.apply_symm_apply] at hp
      rw [hp,← twoElectronConfigurationProduct_snd_position,
        twoElectronConfigurationProduct.apply_symm_apply,norm_mul,mul_pow]
      ring
    _ = _ := by
      rw [integral_prod_mul (fun x : Configuration 1 => ‖f x‖^2)
        (fun y : Configuration 1 => ‖g y‖^2 / ‖position y 0‖),← ProductL2.norm_sq_integral]

theorem twoElectronTensorGradient_norm_sum (f g : SpatialL2 1)
    (df dg : Coordinate 1 → SpatialL2 1) :
    (∑ k : Coordinate 2, ‖twoElectronTensorGradient f g df dg k‖^2) =
      ‖g‖^2 * (∑ k : Coordinate 1, ‖df k‖^2) +
        ‖f‖^2 * (∑ k : Coordinate 1, ‖dg k‖^2) := by
  simp only [Coordinate,Fintype.sum_prod_type,Fin.sum_univ_two,Fin.sum_univ_one]
  simp [twoElectronTensorGradient,twoElectronTensor_norm,mul_pow,Finset.mul_sum,mul_comm]

#print axioms twoElectronTensor_nuclear_first
#print axioms twoElectronTensor_nuclear_second
#print axioms twoElectronTensorGradient_norm_sum
end TheoremT.Continuum
