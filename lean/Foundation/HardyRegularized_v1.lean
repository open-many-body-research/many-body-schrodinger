import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Tactic

/-! Regularized Hardy vector-field prerequisites on actual Euclidean R³.
This file does not yet assert Hardy for the project's weak Sobolev domain. -/
noncomputable section
open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace TheoremT.Hardy

abbrev R3 := EuclideanSpace ℝ (Fin 3)

def basisVector (i : Fin 3) : R3 := EuclideanSpace.single i 1

def regularizedField (δ : ℝ) (i : Fin 3) (x : R3) : ℝ :=
  x i * (‖x‖ ^ 2 + δ)⁻¹

theorem regularizedDenominator_pos {δ : ℝ} (hδ : 0 < δ) (x : R3) :
    0 < ‖x‖ ^ 2 + δ := add_pos_of_nonneg_of_pos (sq_nonneg _) hδ

theorem regularizedField_contDiff {δ : ℝ} (hδ : 0 < δ) (i : Fin 3) :
    ContDiff ℝ 1 (regularizedField δ i) := by
  unfold regularizedField
  apply (show ContDiff ℝ 1 (fun x : R3 => x i) from
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff).mul
  apply ContDiff.inv
  · exact (contDiff_norm_sq ℝ).add contDiff_const
  · exact fun x => (regularizedDenominator_pos hδ x).ne'

theorem regularizedField_directional_derivative {δ : ℝ} (hδ : 0 < δ)
    (i : Fin 3) (x : R3) :
    fderiv ℝ (regularizedField δ i) x (basisVector i) =
      (‖x‖ ^ 2 + δ)⁻¹ - 2 * (x i)^2 * ((‖x‖ ^ 2 + δ)^2)⁻¹ := by
  have hd := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.add_const δ
  have hi := (hasFDerivAt_inv (regularizedDenominator_pos hδ x).ne').comp x hd
  have hc := (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt (x := x)
  have hh := hc.mul hi
  change HasFDerivAt (fun y : R3 => y i * (‖y‖ ^ 2 + δ)⁻¹) _ x at hh
  change fderiv ℝ (fun y : R3 => y i * (‖y‖ ^ 2 + δ)⁻¹) x (basisVector i) = _
  rw [hh.fderiv]
  simp [basisVector, EuclideanSpace.inner_single_right]
  ring

theorem integral_mul_fderiv_compact {u w : R3 → ℝ}
    (hu : ContDiff ℝ 1 u) (hw : ContDiff ℝ 1 w)
    (huc : HasCompactSupport u) (v : R3) :
    (∫ x, u x * fderiv ℝ w x v) = -(∫ x, fderiv ℝ u x v * w x) := by
  have hdu : Continuous (fun x => fderiv ℝ u x v) :=
    (hu.continuous_fderiv_apply (by norm_num)).comp (continuous_id.prodMk continuous_const)
  have hdw : Continuous (fun x => fderiv ℝ w x v) :=
    (hw.continuous_fderiv_apply (by norm_num)).comp (continuous_id.prodMk continuous_const)
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact (hdu.mul hw.continuous).integrable_of_hasCompactSupport
      (huc.fderiv_apply ℝ v).mul_right
  · exact (hu.continuous.mul hdw).integrable_of_hasCompactSupport huc.mul_right
  · exact (hu.continuous.mul hw.continuous).integrable_of_hasCompactSupport huc.mul_right
  · intro x _
    exact hu.differentiable (by norm_num) x
  · intro x _
    exact hw.differentiable (by norm_num) x

#print axioms regularizedField_directional_derivative
#print axioms integral_mul_fderiv_compact
end TheoremT.Hardy
