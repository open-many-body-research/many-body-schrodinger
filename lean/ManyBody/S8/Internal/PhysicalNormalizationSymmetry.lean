import ManyBody.S8.Internal.NormalizedPhysicalH2Approximation
import ConfigurationRotation_v1

/-! Real inverse-norm normalization preserves actual physical exchange and
simultaneous orthogonal rotation symmetries, and actual AE reality. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace ManyBody.S8
open TheoremT.Continuum

theorem physical_normalization_permutation {F : SpatialL2 2}
    (π : Equiv.Perm (Fin 2)) (hF : pullback π F=F) :
    pullback π (physicalNormalizationScalar F • F)=physicalNormalizationScalar F • F := by
  rw [map_smul,hF]

theorem physical_normalization_rotation {F : SpatialL2 2}
    (Q : Position ≃ₗᵢ[ℝ] Position) (hF : spatialRotation 2 Q F=F) :
    spatialRotation 2 Q (physicalNormalizationScalar F • F)=physicalNormalizationScalar F • F := by
  rw [map_smul,hF]

theorem physical_normalization_real {F : SpatialL2 2} (hF : ∀ᵐ x, (F x).im=0) :
    ∀ᵐ x, ((physicalNormalizationScalar F • F : SpatialL2 2) x).im=0 := by
  filter_upwards [Lp.coeFn_smul (physicalNormalizationScalar F) F,hF] with x hx hr
  change (physicalNormalizationScalar F • F : SpatialL2 2) x=physicalNormalizationScalar F • F x at hx
  rw [hx]
  simp only [physicalNormalizationScalar,smul_eq_mul,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,hr,mul_zero,zero_mul,add_zero]

#print axioms physical_normalization_permutation
#print axioms physical_normalization_rotation
#print axioms physical_normalization_real
end ManyBody.S8
