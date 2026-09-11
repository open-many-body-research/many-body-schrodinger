import HydrogenRadialCalculus_v1

/-! All mixed derivatives of the regularized actual one-electron radial profile.
The regularization parameter is strictly positive. -/
noncomputable section
set_option maxHeartbeats 1600000
open scoped BigOperators RealInnerProductSpace ContDiff
namespace TheoremT.Continuum

theorem hydrogenSmoothRadialField_mixed_derivative {δ : ℝ} (hδ : 0 < δ)
    (k l : Coordinate 1) (x : Configuration 1) :
    fderiv ℝ (hydrogenSmoothRadialField δ k) x (coordinateVector l) =
      (if k = l then 1 else 0) / Real.sqrt (‖x‖^2 + δ) -
        x k * x l / (Real.sqrt (‖x‖^2 + δ))^3 := by
  by_cases hkl : k = l
  · subst l
    simpa [pow_two] using
      hydrogenSmoothRadialField_diagonal_derivative hδ k x
  · have hden := hydrogenSmooth_denominator_pos hδ x
    have hs := (Real.sqrt_pos.2 hden).ne'
    have hd := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.add_const δ).sqrt hden.ne'
    have hc := (EuclideanSpace.proj (𝕜 := ℝ) k).hasFDerivAt (x := x)
    have hh := hc.mul ((hasFDerivAt_inv hs).comp x hd)
    change HasFDerivAt (fun y : Configuration 1 => y k * (Real.sqrt (‖y‖^2 + δ))⁻¹) _ x at hh
    unfold hydrogenSmoothRadialField
    simp only [div_eq_mul_inv]
    rw [hh.fderiv]
    simp [coordinateVector, EuclideanSpace.inner_single_right, hkl, Ne.symm hkl]
    field_simp
    <;> ring

theorem hydrogenSmoothReal_first_contDiff {δ : ℝ} (hδ : 0 < δ) (Z : ℝ)
    (k : Coordinate 1) :
    ContDiff ℝ ∞ (fun y => fderiv ℝ (hydrogenSmoothReal Z δ) y (coordinateVector k)) := by
  have he : (fun y => fderiv ℝ (hydrogenSmoothReal Z δ) y (coordinateVector k)) =
      fun y => -Z * hydrogenSmoothRadialField δ k y * hydrogenSmoothReal Z δ y := by
    funext y
    rw [hydrogenSmoothReal_first_derivative hδ]
    simp only [hydrogenSmoothRadialField]
    ring
  rw [he]
  exact (contDiff_const.mul (hydrogenSmoothRadialField_contDiff hδ k)).mul
    (hydrogenSmoothReal_contDiff hδ Z)

theorem hydrogenSmoothReal_mixed_second_derivative {δ : ℝ} (hδ : 0 < δ) (Z : ℝ)
    (k l : Coordinate 1) (x : Configuration 1) :
    fderiv ℝ (fun y => fderiv ℝ (hydrogenSmoothReal Z δ) y (coordinateVector k))
      x (coordinateVector l) =
      (Z^2 * x k * x l / (‖x‖^2 + δ) -
        Z * (if k = l then 1 else 0) / Real.sqrt (‖x‖^2 + δ) +
        Z * x k * x l / (Real.sqrt (‖x‖^2 + δ))^3) * hydrogenSmoothReal Z δ x := by
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
  rw [hydrogenSmoothRadialField_mixed_derivative hδ,
    hydrogenSmoothReal_first_derivative hδ]
  have hs := Real.sq_sqrt (le_of_lt (hydrogenSmooth_denominator_pos hδ x))
  have hn := (Real.sqrt_pos.2 (hydrogenSmooth_denominator_pos hδ x)).ne'
  simp only [hydrogenSmoothRadialField]
  field_simp
  simp only [hs]
  ring

theorem hydrogen_fderiv_ofReal {f : Configuration 1 → ℝ} {x : Configuration 1}
    (hf : DifferentiableAt ℝ f x) (v : Configuration 1) :
    fderiv ℝ (fun y => (f y : ℂ)) x v = (fderiv ℝ f x v : ℂ) := by
  have h := (Complex.ofRealCLM.hasFDerivAt (x := f x)).comp x hf.hasFDerivAt
  change HasFDerivAt (fun y => (f y : ℂ)) _ x at h
  rw [h.fderiv]
  rfl

theorem hydrogenSmooth_first_derivative {δ : ℝ} (hδ : 0 < δ) (Z : ℝ)
    (k : Coordinate 1) (x : Configuration 1) :
    fderiv ℝ (hydrogenSmooth Z δ) x (coordinateVector k) =
      ((-Z * x k / Real.sqrt (‖x‖^2 + δ) : ℝ) : ℂ) * hydrogenSmooth Z δ x := by
  unfold hydrogenSmooth
  rw [hydrogen_fderiv_ofReal ((hydrogenSmoothReal_contDiff hδ Z).differentiable (by simp) x),
    hydrogenSmoothReal_first_derivative hδ]
  exact Complex.ofReal_mul _ _

theorem hydrogenSmooth_first_contDiff {δ : ℝ} (hδ : 0 < δ) (Z : ℝ)
    (k : Coordinate 1) :
    ContDiff ℝ ∞ (fun y => fderiv ℝ (hydrogenSmooth Z δ) y (coordinateVector k)) := by
  have he : (fun y => fderiv ℝ (hydrogenSmooth Z δ) y (coordinateVector k)) =
      fun y => (fderiv ℝ (hydrogenSmoothReal Z δ) y (coordinateVector k) : ℂ) := by
    funext y
    exact hydrogen_fderiv_ofReal ((hydrogenSmoothReal_contDiff hδ Z).differentiable (by simp) y) _
  rw [he]
  exact Complex.ofRealCLM.contDiff.comp (hydrogenSmoothReal_first_contDiff hδ Z k)

theorem hydrogenSmooth_mixed_second_derivative {δ : ℝ} (hδ : 0 < δ) (Z : ℝ)
    (k l : Coordinate 1) (x : Configuration 1) :
    fderiv ℝ (fun y => fderiv ℝ (hydrogenSmooth Z δ) y (coordinateVector k))
      x (coordinateVector l) =
      ((Z^2 * x k * x l / (‖x‖^2 + δ) -
        Z * (if k = l then 1 else 0) / Real.sqrt (‖x‖^2 + δ) +
        Z * x k * x l / (Real.sqrt (‖x‖^2 + δ))^3 : ℝ) : ℂ) * hydrogenSmooth Z δ x := by
  have he : (fun y => fderiv ℝ (hydrogenSmooth Z δ) y (coordinateVector k)) =
      fun y => (fderiv ℝ (hydrogenSmoothReal Z δ) y (coordinateVector k) : ℂ) := by
    funext y
    exact hydrogen_fderiv_ofReal ((hydrogenSmoothReal_contDiff hδ Z).differentiable (by simp) y) _
  rw [he, hydrogen_fderiv_ofReal
    ((hydrogenSmoothReal_first_contDiff hδ Z k).differentiable (by simp) x),
    hydrogenSmoothReal_mixed_second_derivative hδ]
  exact Complex.ofReal_mul _ _

#print axioms hydrogenSmoothRadialField_mixed_derivative
#print axioms hydrogenSmoothReal_first_contDiff
#print axioms hydrogenSmoothReal_mixed_second_derivative
#print axioms hydrogenSmooth_first_derivative
#print axioms hydrogenSmooth_first_contDiff
#print axioms hydrogenSmooth_mixed_second_derivative
end TheoremT.Continuum
