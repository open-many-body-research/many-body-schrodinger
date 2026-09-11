import HydrogenWeak_v1
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Explicit classical derivatives of the strictly regularized hydrogen radial
profile on the actual one-electron configuration space. No assertion of classical
differentiability at the origin is made for the unregularized profile. -/
noncomputable section
set_option maxHeartbeats 1600000
open scoped BigOperators RealInnerProductSpace ContDiff
namespace TheoremT.Continuum

def hydrogenSmoothReal (Z δ : ℝ) (x : Configuration 1) : ℝ :=
  Real.exp (-Z * Real.sqrt (‖x‖^2 + δ))

def hydrogenSmooth (Z δ : ℝ) (x : Configuration 1) : ℂ :=
  (hydrogenSmoothReal Z δ x : ℂ)

def hydrogenSmoothRadialField (δ : ℝ) (k : Coordinate 1) (x : Configuration 1) : ℝ :=
  x k / Real.sqrt (‖x‖^2 + δ)

theorem hydrogenSmooth_denominator_pos {δ : ℝ} (hδ : 0 < δ) (x : Configuration 1) :
    0 < ‖x‖^2 + δ := by positivity

theorem hydrogenSmoothReal_contDiff {δ : ℝ} (hδ : 0 < δ) (Z : ℝ) :
    ContDiff ℝ ∞ (hydrogenSmoothReal Z δ) := by
  have hs : ContDiff ℝ ∞ (fun x : Configuration 1 => Real.sqrt (‖x‖^2 + δ)) :=
    ((contDiff_norm_sq ℝ).add contDiff_const).sqrt
      (fun x => (hydrogenSmooth_denominator_pos hδ x).ne')
  exact (contDiff_const.mul hs).exp

theorem hydrogenSmooth_contDiff {δ : ℝ} (hδ : 0 < δ) (Z : ℝ) :
    ContDiff ℝ ∞ (hydrogenSmooth Z δ) :=
  Complex.ofRealCLM.contDiff.comp (hydrogenSmoothReal_contDiff hδ Z)

theorem hydrogenSmoothRadialField_contDiff {δ : ℝ} (hδ : 0 < δ) (k : Coordinate 1) :
    ContDiff ℝ ∞ (hydrogenSmoothRadialField δ k) := by
  apply (EuclideanSpace.proj (𝕜 := ℝ) k).contDiff.div
  · exact ((contDiff_norm_sq ℝ).add contDiff_const).sqrt
      (fun x => (hydrogenSmooth_denominator_pos hδ x).ne')
  · exact fun x => (Real.sqrt_pos.2 (hydrogenSmooth_denominator_pos hδ x)).ne'

theorem hydrogenSmoothRadialField_diagonal_derivative {δ : ℝ} (hδ : 0 < δ)
    (k : Coordinate 1) (x : Configuration 1) :
    fderiv ℝ (hydrogenSmoothRadialField δ k) x (coordinateVector k) =
      (Real.sqrt (‖x‖^2 + δ))⁻¹ - (x k)^2 / (Real.sqrt (‖x‖^2 + δ))^3 := by
  have hden := hydrogenSmooth_denominator_pos hδ x
  have hs := (Real.sqrt_pos.2 hden).ne'
  have hd := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.add_const δ).sqrt hden.ne'
  have hc := (EuclideanSpace.proj (𝕜 := ℝ) k).hasFDerivAt (x := x)
  have hh := hc.mul ((hasFDerivAt_inv hs).comp x hd)
  change HasFDerivAt (fun y : Configuration 1 => y k * (Real.sqrt (‖y‖^2 + δ))⁻¹) _ x at hh
  unfold hydrogenSmoothRadialField
  simp only [div_eq_mul_inv]
  rw [hh.fderiv]
  simp [coordinateVector, EuclideanSpace.inner_single_right]
  field_simp
  <;> ring

theorem hydrogenSmoothReal_first_derivative {δ : ℝ} (hδ : 0 < δ) (Z : ℝ)
    (k : Coordinate 1) (x : Configuration 1) :
    fderiv ℝ (hydrogenSmoothReal Z δ) x (coordinateVector k) =
      (-Z * x k / Real.sqrt (‖x‖^2 + δ)) * hydrogenSmoothReal Z δ x := by
  have hden := hydrogenSmooth_denominator_pos hδ x
  have hs := (Real.sqrt_pos.2 hden).ne'
  have hd := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.add_const δ).sqrt hden.ne'
  have hh := (hd.const_mul (-Z)).exp
  unfold hydrogenSmoothReal
  rw [hh.fderiv]
  simp [coordinateVector, EuclideanSpace.inner_single_right]
  field_simp
  <;> ring

theorem hydrogenSmoothReal_diagonal_second_derivative {δ : ℝ} (hδ : 0 < δ) (Z : ℝ)
    (k : Coordinate 1) (x : Configuration 1) :
    fderiv ℝ (fun y => fderiv ℝ (hydrogenSmoothReal Z δ) y (coordinateVector k))
      x (coordinateVector k) =
      (Z^2 * (x k)^2 / (‖x‖^2 + δ) - Z / Real.sqrt (‖x‖^2 + δ) +
        Z * (x k)^2 / (Real.sqrt (‖x‖^2 + δ))^3) * hydrogenSmoothReal Z δ x := by
  have he : (fun y => fderiv ℝ (hydrogenSmoothReal Z δ) y (coordinateVector k)) =
      fun y => -Z * hydrogenSmoothRadialField δ k y * hydrogenSmoothReal Z δ y := by
    funext y
    rw [hydrogenSmoothReal_first_derivative hδ]
    simp only [hydrogenSmoothRadialField]
    ring
  rw [he]
  have hf := ((hydrogenSmoothReal_contDiff hδ Z).differentiable (by simp) x).hasFDerivAt
  have hr := ((hydrogenSmoothRadialField_contDiff hδ k).differentiable (by simp) x).hasFDerivAt
  have hh := (hr.const_mul (-Z)).mul hf
  change HasFDerivAt (fun y : Configuration 1 =>
    -Z * hydrogenSmoothRadialField δ k y * hydrogenSmoothReal Z δ y) _ x at hh
  rw [hh.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [hydrogenSmoothRadialField_diagonal_derivative hδ,
    hydrogenSmoothReal_first_derivative hδ]
  have hs := Real.sq_sqrt (le_of_lt (hydrogenSmooth_denominator_pos hδ x))
  have hn := (Real.sqrt_pos.2 (hydrogenSmooth_denominator_pos hδ x)).ne'
  simp only [hydrogenSmoothRadialField]
  field_simp
  simp only [hs]
  ring

#print axioms hydrogenSmoothReal_contDiff
#print axioms hydrogenSmooth_contDiff
#print axioms hydrogenSmoothRadialField_diagonal_derivative
#print axioms hydrogenSmoothReal_first_derivative
#print axioms hydrogenSmoothReal_diagonal_second_derivative

end TheoremT.Continuum
