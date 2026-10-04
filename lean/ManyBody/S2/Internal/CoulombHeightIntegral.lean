import PolarThree_v1
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! An exact Coulomb height integral, proved by the fundamental theorem
of calculus on a nonsingular interval. This is an analytic ingredient of the
three-dimensional Newton shell average, with no supplied moment formula.
-/
noncomputable section
open MeasureTheory Set
namespace ManyBody.S2.Internal.CoulombAngular

theorem kernel_radicand_pos (r s : ℝ) (_hr : 0 < r) (hs : 0 < s)
    (hrs : r ≠ s) {z : ℝ} (hz : z ∈ Icc (-r) r) :
    0 < r^2+s^2-2*s*z := by
  have hd : 0 < (r-s)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hrs)
  have hx : 0 ≤ 2*s*(r-z) := mul_nonneg (by positivity) (sub_nonneg.mpr hz.2)
  nlinarith

/-- The actual one-dimensional Coulomb angular integral, with no moment premise. -/
theorem integral_coulomb_height (r s : ℝ) (hr : 0 < r) (hs : 0 < s)
    (hrs : r ≠ s) :
    (∫ z : ℝ in (-r)..r, (Real.sqrt (r^2+s^2-2*s*z))⁻¹) =
      2*r / max r s := by
  have hle : -r ≤ r := by linarith
  have hpos (z : ℝ) (hz : z ∈ Icc (-r) r) := kernel_radicand_pos r s hr hs hrs hz
  have hcont : ContinuousOn (fun z : ℝ => (Real.sqrt (r^2+s^2-2*s*z))⁻¹)
      (Icc (-r) r) := by
    apply ContinuousOn.inv₀
    · fun_prop
    · intro z hz
      exact (Real.sqrt_pos.mpr (hpos z hz)).ne'
  have hderiv (z : ℝ) (hz : z ∈ Ioo (-r) r) :
      HasDerivAt (fun z : ℝ => -(Real.sqrt (r^2+s^2-2*s*z))/s)
        ((Real.sqrt (r^2+s^2-2*s*z))⁻¹) z := by
    have hrad := ((hasDerivAt_const z (r^2+s^2)).sub
      ((hasDerivAt_id z).const_mul (2*s))).sqrt
        (ne_of_gt (hpos z ⟨hz.1.le,hz.2.le⟩))
    convert! hrad.neg.div_const s using 1
    dsimp
    field_simp [hs.ne', (Real.sqrt_pos.mpr (hpos z ⟨hz.1.le,hz.2.le⟩)).ne']
    ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle
    (f := fun z : ℝ => -(Real.sqrt (r^2+s^2-2*s*z))/s)
    (by fun_prop) hderiv (hcont.intervalIntegrable_of_Icc hle)
  have hp : r^2+s^2-2*s*(-r) = (r+s)^2 := by ring
  have hm : r^2+s^2-2*s*r = (r-s)^2 := by ring
  rw [hp,hm,Real.sqrt_sq_eq_abs,Real.sqrt_sq (by linarith : 0 ≤ r+s)] at he
  rw [he]
  by_cases h : r ≤ s
  · rw [max_eq_right h,abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [max_eq_left (le_of_not_ge h),abs_of_pos (sub_pos.mpr (lt_of_not_ge h))]
    field_simp [hs.ne',hr.ne']
    ring

#print axioms integral_coulomb_height
end ManyBody.S2.Internal.CoulombAngular
