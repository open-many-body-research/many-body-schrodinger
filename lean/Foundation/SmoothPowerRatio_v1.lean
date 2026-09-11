import RegularizedComplexNorm_v1
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! A smooth radial truncation ratio. Parameters a,b are squared positive
regularization/cap radii. The estimates hold on s>=0, the actual squared norm. -/
noncomputable section
namespace TheoremT.Continuum

def smoothPowerRatio (a b s : ℝ) : ℝ := b*(a+s)/(b+s)

def smoothPowerSlope (a b s : ℝ) : ℝ := (b-a)/((a+s)*(b+s))

theorem smoothPowerRatio_pos {a b s : ℝ} (ha : 0 < a) (hab : a ≤ b) (hs : 0 ≤ s) :
    0 < smoothPowerRatio a b s := by
  have hb : 0 < b := ha.trans_le hab
  unfold smoothPowerRatio
  positivity

theorem smoothPowerRatio_le_cap {a b s : ℝ} (ha : 0 < a) (hab : a ≤ b) (hs : 0 ≤ s) :
    smoothPowerRatio a b s ≤ b := by
  have hb : 0 < b := ha.trans_le hab
  unfold smoothPowerRatio
  apply (div_le_iff₀ (by positivity : 0 < b+s)).mpr
  nlinarith

theorem smoothPowerRatio_le_input {a b s : ℝ} (ha : 0 < a) (hab : a ≤ b) (hs : 0 ≤ s) :
    smoothPowerRatio a b s ≤ a+s := by
  have hb : 0 < b := ha.trans_le hab
  unfold smoothPowerRatio
  apply (div_le_iff₀ (by positivity : 0 < b+s)).mpr
  nlinarith

theorem smoothPowerSlope_nonneg {a b s : ℝ} (ha : 0 < a) (hab : a ≤ b) (hs : 0 ≤ s) :
    0 ≤ smoothPowerSlope a b s := by
  have hb : 0 < b := ha.trans_le hab
  exact div_nonneg (sub_nonneg.mpr hab) (by positivity)

theorem smoothPowerSlope_bound {a b s : ℝ} (ha : 0 < a) (hab : a ≤ b) (hs : 0 ≤ s) :
    s*smoothPowerSlope a b s ≤ 1 := by
  have hb : 0 < b := ha.trans_le hab
  unfold smoothPowerSlope
  rw [← mul_div_assoc]
  apply (div_le_one (by positivity : 0 < (a+s)*(b+s))).mpr
  nlinarith

theorem smoothPowerRatio_hasDerivAt {a b s : ℝ} (ha : 0 < a) (hab : a ≤ b) (hs : 0 ≤ s) :
    HasDerivAt (smoothPowerRatio a b)
      (smoothPowerRatio a b s*smoothPowerSlope a b s) s := by
  have hb : 0 < b := ha.trans_le hab
  have ha' : a+s ≠ 0 := by positivity
  have hb' : b+s ≠ 0 := by positivity
  have hh := (((hasDerivAt_id s).const_add a).const_mul b).div
    ((hasDerivAt_id s).const_add b) hb'
  convert! hh using 1
  unfold smoothPowerRatio smoothPowerSlope
  simp only [id_eq]
  field_simp
  <;> ring

theorem smoothPowerRatio_rpow_hasDerivAt {a b s r : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hs : 0 ≤ s) :
    HasDerivAt (fun t => (smoothPowerRatio a b t)^r)
      (r*(smoothPowerRatio a b s)^r*smoothPowerSlope a b s) s := by
  have hp := smoothPowerRatio_pos ha hab hs
  have h := (smoothPowerRatio_hasDerivAt ha hab hs).rpow_const (p := r) (Or.inl hp.ne')
  rw [Real.rpow_sub_one hp.ne'] at h
  convert! h using 1
  field_simp

theorem smoothPowerAmplitude_slope_bound {a b s r : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hs : 0 ≤ s) (hr : 0 ≤ r) :
    s*(r*(smoothPowerRatio a b s)^r*smoothPowerSlope a b s) ≤
      r*(smoothPowerRatio a b s)^r := by
  have h := mul_le_mul_of_nonneg_left (smoothPowerSlope_bound ha hab hs)
    (mul_nonneg hr (Real.rpow_nonneg (smoothPowerRatio_pos ha hab hs).le r))
  nlinarith

#print axioms smoothPowerRatio_hasDerivAt
#print axioms smoothPowerRatio_rpow_hasDerivAt
#print axioms smoothPowerAmplitude_slope_bound
end TheoremT.Continuum
