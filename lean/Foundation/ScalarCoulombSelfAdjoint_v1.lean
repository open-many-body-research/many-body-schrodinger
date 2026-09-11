import ScalarCoulombOperator_v1
import HardyCoulombSelfAdjoint_v1

/-! Actual scalar all-N Coulomb self-adjointness on precisely weak H².
The scalar Fourier free resolvent and proved scalar Hardy multiplier estimate
supply the small-error inverse construction. No fermionic restriction, spectral
premise, eigenfunction, compactness, or attainment premise is imposed. -/
noncomputable section
open MeasureTheory
open scoped BigOperators LinearPMap
namespace TheoremT.Continuum

theorem scalarFreeResolvent_mem_domain (N : ℕ) (Z : ℝ) {μ : ℝ} (hμ : 0 < μ)
    (f : SpatialL2 N) : freeResolvent N μ hμ f ∈ (scalarCoulombOperator N Z).domain := by
  rw [scalarCoulombOperator_domain_iff_H2]
  exact freeResolvent_hasH2 N hμ f

def scalarFreeResolventToDomain (N : ℕ) (Z μ : ℝ) (hμ : 0 < μ) :
    SpatialL2 N →ₗ[ℂ] (scalarCoulombOperator N Z).domain :=
  (freeResolvent N μ hμ).toLinearMap.codRestrict _ (scalarFreeResolvent_mem_domain N Z hμ)

def scalarCoulombFreeErrorLinear (N : ℕ) (Z μ : ℝ) (hμ : 0 < μ) :
    SpatialL2 N →ₗ[ℂ] SpatialL2 N :=
  (scalarCoulombOperator N Z).toFun.comp (scalarFreeResolventToDomain N Z μ hμ) +
    (μ : ℂ) • (freeResolvent N μ hμ).toLinearMap - LinearMap.id

theorem scalarCoulombFreeErrorLinear_apply_ae (N : ℕ) (Z : ℝ) {μ : ℝ}
    (hμ : 0 < μ) (f : SpatialL2 N) :
    scalarCoulombFreeErrorLinear N Z μ hμ f =ᵐ[volume]
      fun x => (coulombPotential N Z x : ℂ)*(freeResolvent N μ hμ f) x := by
  have hfree : positiveFreeGraph μ (freeResolvent N μ hμ f) f := by
    simpa only [positiveFreeGraph, neg_div] using freeResolvent_solve N hμ f
  exact positiveFreeGraph_coulomb_error_ae hfree
    (scalarCoulombOperator_apply_graph N Z (scalarFreeResolventToDomain N Z μ hμ f))

theorem scalarCoulombFreeErrorLinear_norm_le (N : ℕ) (Z : ℝ) {μ : ℝ}
    (hμ : 0 < μ) (f : SpatialL2 N) :
    ‖scalarCoulombFreeErrorLinear N Z μ hμ f‖ ≤
      (coulombFreeBoundConstant N Z / Real.sqrt (2*μ))*‖f‖ := by
  obtain ⟨d,e,hd,he,hout⟩ := freeResolvent_solve N hμ f
  have hb := coulomb_product_norm_le Z (freeResolvent N μ hμ f) d hd
    (scalarCoulombFreeErrorLinear N Z μ hμ f) (scalarCoulombFreeErrorLinear_apply_ae N Z hμ f)
  have hout' : f = (-1/2 : ℝ) • (∑ k, e k k) + μ • freeResolvent N μ hμ f := by
    simpa only [neg_div] using hout
  have hg := positiveFreeGraph_gradient_sq_le hμ d e hd he hout'
  change ‖scalarCoulombFreeErrorLinear N Z μ hμ f‖ ≤
    coulombFreeBoundConstant N Z * Real.sqrt (∑ k, ‖d k‖^2) at hb
  calc
    ‖scalarCoulombFreeErrorLinear N Z μ hμ f‖ ≤
        coulombFreeBoundConstant N Z * Real.sqrt (∑ k, ‖d k‖^2) := hb
    _ ≤ coulombFreeBoundConstant N Z * Real.sqrt (‖f‖^2/(2*μ)) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hg) (coulombFreeBoundConstant_nonneg N Z)
    _ = (coulombFreeBoundConstant N Z / Real.sqrt (2*μ))*‖f‖ := by
      rw [Real.sqrt_div (sq_nonneg _),Real.sqrt_sq_eq_abs,abs_norm]
      ring

def scalarCoulombFreeError (N : ℕ) (Z μ : ℝ) (hμ : 0 < μ) :
    SpatialL2 N →L[ℂ] SpatialL2 N :=
  (scalarCoulombFreeErrorLinear N Z μ hμ).mkContinuous
    (coulombFreeBoundConstant N Z / Real.sqrt (2*μ))
    (scalarCoulombFreeErrorLinear_norm_le N Z hμ)

theorem norm_scalarCoulombFreeError_le (N : ℕ) (Z : ℝ) {μ : ℝ} (hμ : 0 < μ) :
    ‖scalarCoulombFreeError N Z μ hμ‖ ≤ coulombFreeBoundConstant N Z / Real.sqrt (2*μ) := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (div_nonneg (coulombFreeBoundConstant_nonneg N Z) (Real.sqrt_nonneg _))
  exact scalarCoulombFreeErrorLinear_norm_le N Z hμ

theorem scalarCoulombFreeError_identity (N : ℕ) (Z : ℝ) {μ : ℝ} (hμ : 0 < μ)
    (f : SpatialL2 N) :
    (scalarCoulombOperator N Z) (scalarFreeResolventToDomain N Z μ hμ f) +
      (μ : ℂ) • freeResolvent N μ hμ f = f + scalarCoulombFreeError N Z μ hμ f := by
  change _ = f + (((scalarCoulombOperator N Z) (scalarFreeResolventToDomain N Z μ hμ f) +
    (μ : ℂ) • freeResolvent N μ hμ f) - f)
  abel

theorem scalarCoulombFreeError_shift_norm_lt_one (N : ℕ) (Z : ℝ) :
    ‖scalarCoulombFreeError N Z (coulombSelfAdjointShift N Z)
      (coulombSelfAdjointShift_pos N Z)‖ < 1 := by
  apply lt_of_le_of_lt (norm_scalarCoulombFreeError_le N Z (coulombSelfAdjointShift_pos N Z))
  have hsqrt : 0 < Real.sqrt (2*coulombSelfAdjointShift N Z) :=
    Real.sqrt_pos.mpr (mul_pos (by norm_num) (coulombSelfAdjointShift_pos N Z))
  apply (div_lt_one hsqrt).mpr
  apply (Real.lt_sqrt (coulombFreeBoundConstant_nonneg N Z)).mpr
  unfold coulombSelfAdjointShift
  nlinarith [sq_nonneg (coulombFreeBoundConstant N Z)]

theorem scalarCoulombOperator_selfAdjoint (N : ℕ) (Z : ℝ) :
    IsSelfAdjoint (scalarCoulombOperator N Z) := by
  let μ := coulombSelfAdjointShift N Z
  have hμ : 0 < μ := coulombSelfAdjointShift_pos N Z
  apply TheoremT.OperatorTheory.selfAdjoint_of_small_resolvent_error
    (scalarCoulombOperator N Z) μ (scalarCoulombOperator_domain_dense N Z)
    (fun f g => (scalarCoulombOperator_symmetric N Z f g).symm)
    (freeResolvent N μ hμ) (scalarCoulombFreeError N Z μ hμ)
    (scalarFreeResolvent_mem_domain N Z hμ)
  · exact scalarCoulombFreeError_identity N Z hμ
  · exact scalarCoulombFreeError_shift_norm_lt_one N Z

theorem scalarCoulombOperator_selfAdjoint_exact_H2 (N : ℕ) (Z : ℝ) :
    IsSelfAdjoint (scalarCoulombOperator N Z) ∧
      ((scalarCoulombOperator N Z).domain : Set (SpatialL2 N)) = {f | HasH2 f} :=
  ⟨scalarCoulombOperator_selfAdjoint N Z,scalarCoulombOperator_domain_eq_H2 N Z⟩

#print axioms scalarCoulombFreeErrorLinear_apply_ae
#print axioms scalarCoulombFreeErrorLinear_norm_le
#print axioms scalarCoulombOperator_selfAdjoint
#print axioms scalarCoulombOperator_selfAdjoint_exact_H2
end TheoremT.Continuum
