import SmoothPowerRatio_v1
import RadialPowerNormBound_v1

/-! Actual smooth bounded-derivative radial power maps on complex values.
For a>0, b>=a and r>=0, the cap is finite and the logarithmic slope is bounded
uniformly in a,b. These are the concrete nonlinear maps used in H1 tests. -/
noncomputable section
open scoped ContDiff
namespace TheoremT.Continuum

def smoothRadialAmplitude (a b r : ℝ) (z : ℂ) : ℝ := (smoothPowerRatio a b (‖z‖^2))^r

def smoothRadialAmplitudeSlope (a b r : ℝ) (z : ℂ) : ℝ :=
  r*smoothRadialAmplitude a b r z*smoothPowerSlope a b (‖z‖^2)

def smoothRadialPower (a b r : ℝ) (z : ℂ) : ℂ := smoothRadialAmplitude a b r z • z

theorem smoothRadialAmplitude_pos {a b r : ℝ} (ha : 0 < a) (hab : a ≤ b) (z : ℂ) :
    0 < smoothRadialAmplitude a b r z :=
  Real.rpow_pos_of_pos (smoothPowerRatio_pos ha hab (sq_nonneg _)) _

theorem smoothRadialAmplitude_contDiff {a b r : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ContDiff ℝ ∞ (smoothRadialAmplitude a b r) := by
  have hb : 0 < b := ha.trans_le hab
  have hq : ContDiff ℝ ∞ (fun z : ℂ => smoothPowerRatio a b (‖z‖^2)) := by
    unfold smoothPowerRatio
    exact (contDiff_const.mul (contDiff_const.add (contDiff_norm_sq ℝ))).div
      (contDiff_const.add (contDiff_norm_sq ℝ)) (fun z => by positivity)
  exact hq.rpow_const_of_ne (fun z => (smoothPowerRatio_pos ha hab (sq_nonneg _)).ne')

theorem smoothRadialPower_contDiff {a b r : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ContDiff ℝ ∞ (smoothRadialPower a b r) :=
  (smoothRadialAmplitude_contDiff ha hab).smul contDiff_id

theorem smoothRadialPower_zero (a b r : ℝ) : smoothRadialPower a b r 0 = 0 := by
  simp [smoothRadialPower]

theorem smoothRadialPower_fderiv {a b r : ℝ} (ha : 0 < a) (hab : a ≤ b) (z w : ℂ) :
    fderiv ℝ (smoothRadialPower a b r) z w =
      radialPowerDerivative (smoothRadialAmplitude a b r z)
        (smoothRadialAmplitudeSlope a b r z) z w := by
  have hnorm : HasFDerivAt (fun y : ℂ => ‖y‖^2) (2 • innerSL ℝ z) z :=
    (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have hh := (smoothPowerRatio_rpow_hasDerivAt (r := r) ha hab (sq_nonneg ‖z‖)).comp_hasFDerivAt z hnorm
  change HasFDerivAt (smoothRadialAmplitude a b r) _ z at hh
  have hj := hh.smul (hasFDerivAt_id z)
  change HasFDerivAt (smoothRadialPower a b r) _ z at hj
  rw [hj.fderiv]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.id_apply,innerSL_apply_apply,
    smul_eq_mul,radialPowerDerivative,smoothRadialAmplitudeSlope,smoothRadialAmplitude,two_smul,id_eq]
  congr 2 <;> ring

theorem smoothRadialAmplitudeSlope_nonneg {a b r : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hr : 0 ≤ r) (z : ℂ) :
    0 ≤ smoothRadialAmplitudeSlope a b r z :=
  mul_nonneg (mul_nonneg hr (smoothRadialAmplitude_pos ha hab z).le)
    (smoothPowerSlope_nonneg ha hab (sq_nonneg _))

theorem smoothRadialAmplitudeSlope_bound {a b r : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hr : 0 ≤ r) (z : ℂ) :
    smoothRadialAmplitudeSlope a b r z*‖z‖^2 ≤ r*smoothRadialAmplitude a b r z := by
  simpa only [smoothRadialAmplitudeSlope,smoothRadialAmplitude,mul_comm] using
    smoothPowerAmplitude_slope_bound ha hab (sq_nonneg ‖z‖) hr

theorem smoothRadialPower_fderiv_norm {a b r : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hr : 0 ≤ r) (z : ℂ) :
    ‖fderiv ℝ (smoothRadialPower a b r) z‖ ≤ (1+2*r)*b^r := by
  have hb : 0 < b := ha.trans_le hab
  have hcap : smoothRadialAmplitude a b r z ≤ b^r :=
    Real.rpow_le_rpow (smoothPowerRatio_pos ha hab (sq_nonneg _)).le
      (smoothPowerRatio_le_cap ha hab (sq_nonneg _)) hr
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  rw [smoothRadialPower_fderiv ha hab]
  apply (radialPowerDerivative_norm_le (smoothRadialAmplitude_pos ha hab z).le
    (smoothRadialAmplitudeSlope_nonneg ha hab hr z) hr z w
    (smoothRadialAmplitudeSlope_bound ha hab hr z)).trans
  have hh := mul_le_mul_of_nonneg_right hcap (show 0 ≤ (1+2*r)*‖w‖ by positivity)
  nlinarith

#print axioms smoothRadialPower_contDiff
#print axioms smoothRadialPower_fderiv
#print axioms smoothRadialPower_fderiv_norm
end TheoremT.Continuum
