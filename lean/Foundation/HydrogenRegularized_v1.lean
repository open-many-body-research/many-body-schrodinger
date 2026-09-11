import HardyRegularized_v2
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Constant-sharp regularized Coulomb completing-square identity on actual R³.
This is a new refinement; the established Hardy sources remain unchanged. -/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped BigOperators RealInnerProductSpace
namespace TheoremT.Hydrogen
open TheoremT.Hardy

def radialField (δ : ℝ) (i : Fin 3) (x : R3) : ℝ :=
  x i / Real.sqrt (‖x‖ ^ 2 + δ)

theorem radialField_contDiff {δ : ℝ} (hδ : 0 < δ) (i : Fin 3) :
    ContDiff ℝ 1 (radialField δ i) := by
  apply (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.div
  · exact ((contDiff_norm_sq ℝ).add contDiff_const).sqrt
      (fun x => (regularizedDenominator_pos hδ x).ne')
  · exact fun x => (Real.sqrt_pos.2 (regularizedDenominator_pos hδ x)).ne'

theorem radialField_directional_derivative {δ : ℝ} (hδ : 0 < δ)
    (i : Fin 3) (x : R3) :
    fderiv ℝ (radialField δ i) x (basisVector i) =
      (Real.sqrt (‖x‖ ^ 2 + δ))⁻¹ - (x i)^2 / (Real.sqrt (‖x‖ ^ 2 + δ))^3 := by
  have hden := regularizedDenominator_pos hδ x
  have hs := (Real.sqrt_pos.2 hden).ne'
  have hd := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.add_const δ).sqrt hden.ne'
  have hc := (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt (x := x)
  have hh := hc.mul ((hasFDerivAt_inv hs).comp x hd)
  change HasFDerivAt (fun y : R3 => y i * (Real.sqrt (‖y‖^2 + δ))⁻¹) _ x at hh
  unfold radialField
  simp only [div_eq_mul_inv]
  rw [hh.fderiv]
  simp [basisVector, EuclideanSpace.inner_single_right]
  field_simp
  <;> ring

def radialWeightedField (δ : ℝ) (u : R3 → ℝ) (i : Fin 3) (x : R3) : ℝ :=
  (u x)^2 * radialField δ i x

theorem radialWeightedField_contDiff {δ : ℝ} (hδ : 0 < δ) {u : R3 → ℝ}
    (hu : ContDiff ℝ 1 u) (i : Fin 3) : ContDiff ℝ 1 (radialWeightedField δ u i) :=
  (hu.pow 2).mul (radialField_contDiff hδ i)

theorem radialWeightedField_compact {δ : ℝ} {u : R3 → ℝ}
    (huc : HasCompactSupport u) (i : Fin 3) : HasCompactSupport (radialWeightedField δ u i) := by
  unfold radialWeightedField
  simp only [sq]
  exact (huc.mul_right (f' := u)).mul_right (f' := radialField δ i)

theorem radialWeightedField_directional_derivative {δ : ℝ} (hδ : 0 < δ)
    {u : R3 → ℝ} (hu : ContDiff ℝ 1 u) (i : Fin 3) (x : R3) :
    fderiv ℝ (radialWeightedField δ u i) x (basisVector i) =
      2 * u x * fderiv ℝ u x (basisVector i) * radialField δ i x +
      (u x)^2 * ((Real.sqrt (‖x‖ ^ 2 + δ))⁻¹ -
        (x i)^2 / (Real.sqrt (‖x‖ ^ 2 + δ))^3) := by
  have hd := (hu.differentiable (by norm_num) x).hasFDerivAt
  have hb := ((radialField_contDiff hδ i).differentiable (by norm_num) x).hasFDerivAt
  have hh := (hd.mul hd).mul hb
  change HasFDerivAt (𝕜 := ℝ) (fun y : R3 => u y * u y * radialField δ i y) _ x at hh
  simp only [← sq] at hh
  unfold radialWeightedField
  rw [hh.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    Pi.pow_apply]
  rw [radialField_directional_derivative hδ]
  ring

theorem radialWeightedField_divergence_integral {δ : ℝ} (hδ : 0 < δ)
    {u : R3 → ℝ} (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u) :
    (∫ x, ∑ i : Fin 3, fderiv ℝ (radialWeightedField δ u i) x (basisVector i)) = 0 := by
  rw [integral_finset_sum]
  · simp_rw [integral_fderiv_compact (radialWeightedField_contDiff hδ hu _)
      (radialWeightedField_compact huc _)]
    simp
  · intro i _
    exact (((radialWeightedField_contDiff hδ hu i).continuous_fderiv_apply (by norm_num)).comp
      (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
        ((radialWeightedField_compact huc i).fderiv_apply ℝ (basisVector i))

#print axioms radialField_directional_derivative
#print axioms radialWeightedField_divergence_integral
end TheoremT.Hydrogen
