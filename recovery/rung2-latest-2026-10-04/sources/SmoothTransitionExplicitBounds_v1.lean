import ExpNegInvGlueExplicitBounds_v1

/-! Conservative numerical first and second derivative bounds for the
actual C-infinity Mathlib transition, obtained without replacing it by a
piecewise polynomial. The constants are 96 and 14016. -/
noncomputable section
open scoped ContDiff
namespace TheoremT.Continuum

def smoothTransitionDenominator (x : ℝ) : ℝ := expNegInvGlue x+expNegInvGlue (1-x)

theorem smoothTransitionDenominator_contDiff :
    ContDiff ℝ ∞ smoothTransitionDenominator :=
  expNegInvGlue.contDiff.add (expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id))

theorem smoothTransitionDenominator_deriv (x : ℝ) :
    deriv smoothTransitionDenominator x = deriv expNegInvGlue x-deriv expNegInvGlue (1-x) := by
  have hg (z : ℝ) := (expNegInvGlue.contDiff : ContDiff ℝ ∞ expNegInvGlue).differentiable
    (by simp) z |>.hasDerivAt
  have hh := ((hg x).add ((hg (1-x)).comp x
    ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)))).deriv
  change deriv smoothTransitionDenominator x =
    deriv expNegInvGlue x+deriv expNegInvGlue (1-x)*(0-1) at hh
  convert hh using 1 <;> ring

theorem smoothTransitionDenominator_second_deriv (x : ℝ) :
    deriv (deriv smoothTransitionDenominator) x =
      deriv (deriv expNegInvGlue) x+deriv (deriv expNegInvGlue) (1-x) := by
  have hg' : ContDiff ℝ ∞ (deriv expNegInvGlue) :=
    (expNegInvGlue.contDiff : ContDiff ℝ ∞ expNegInvGlue).deriv'
  have hg (z : ℝ) := hg'.differentiable (by simp) z |>.hasDerivAt
  have hh := ((hg x).sub ((hg (1-x)).comp x
    ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)))).deriv
  change deriv (fun x => deriv expNegInvGlue x-deriv expNegInvGlue (1-x)) x =
    deriv (deriv expNegInvGlue) x-deriv (deriv expNegInvGlue) (1-x)*(0-1) at hh
  rw [funext smoothTransitionDenominator_deriv]
  convert hh using 1 <;> ring

theorem smoothTransitionDenominator_deriv_bounds (x : ℝ) :
    |deriv smoothTransitionDenominator x| ≤ 4 ∧
      |deriv (deriv smoothTransitionDenominator) x| ≤ 72 := by
  constructor
  · rw [smoothTransitionDenominator_deriv]
    exact (abs_sub _ _).trans (by linarith [expNegInvGlue_deriv_abs_le_two x,
      expNegInvGlue_deriv_abs_le_two (1-x)])
  · rw [smoothTransitionDenominator_second_deriv]
    exact (abs_add_le _ _).trans (by linarith [expNegInvGlue_second_deriv_abs_le_thirty_six x,
      expNegInvGlue_second_deriv_abs_le_thirty_six (1-x)])

theorem smoothTransition_denominator_product (x : ℝ) :
    smoothTransitionDenominator x * Real.smoothTransition x = expNegInvGlue x := by
  unfold smoothTransitionDenominator Real.smoothTransition
  field_simp [(Real.smoothTransition.pos_denom x).ne']

theorem smoothTransition_product_first (x : ℝ) :
    deriv smoothTransitionDenominator x * Real.smoothTransition x +
      smoothTransitionDenominator x * deriv Real.smoothTransition x = deriv expNegInvGlue x := by
  have hd := smoothTransitionDenominator_contDiff.differentiable (by simp) x |>.hasDerivAt
  have ht := (Real.smoothTransition.contDiff : ContDiff ℝ ∞ Real.smoothTransition).differentiable
    (by simp) x |>.hasDerivAt
  have hh := (hd.mul ht).deriv
  change deriv (fun x => smoothTransitionDenominator x*Real.smoothTransition x) x = _ at hh
  rw [funext smoothTransition_denominator_product] at hh
  exact hh.symm

theorem smoothTransition_product_second (x : ℝ) :
    deriv (deriv smoothTransitionDenominator) x * Real.smoothTransition x +
      2*deriv smoothTransitionDenominator x * deriv Real.smoothTransition x +
      smoothTransitionDenominator x * deriv (deriv Real.smoothTransition) x =
        deriv (deriv expNegInvGlue) x := by
  have hd := smoothTransitionDenominator_contDiff.differentiable (by simp) x |>.hasDerivAt
  have hd' : ContDiff ℝ ∞ (deriv smoothTransitionDenominator) := smoothTransitionDenominator_contDiff.deriv'
  have hdd := hd'.differentiable (by simp) x |>.hasDerivAt
  have ht := (Real.smoothTransition.contDiff : ContDiff ℝ ∞ Real.smoothTransition).differentiable
    (by simp) x |>.hasDerivAt
  have ht' : ContDiff ℝ ∞ (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff : ContDiff ℝ ∞ Real.smoothTransition).deriv'
  have htt := ht'.differentiable (by simp) x |>.hasDerivAt
  have hh := ((hdd.mul ht).add (hd.mul htt)).deriv
  change deriv (fun x => deriv smoothTransitionDenominator x*Real.smoothTransition x+
    smoothTransitionDenominator x*deriv Real.smoothTransition x) x = _ at hh
  rw [funext smoothTransition_product_first] at hh
  linarith

theorem smoothTransition_deriv_abs_le_ninety_six (x : ℝ) :
    |deriv Real.smoothTransition x| ≤ 96 := by
  have hD : (1/16 : ℝ) ≤ smoothTransitionDenominator x := smoothTransition_denom_lower x
  have hD0 : 0 ≤ smoothTransitionDenominator x := by linarith
  have ht : |Real.smoothTransition x| ≤ 1 := by
    rw [abs_of_nonneg (Real.smoothTransition.nonneg x)]
    exact Real.smoothTransition.le_one x
  have hprod : |deriv smoothTransitionDenominator x * Real.smoothTransition x| ≤ 4 := by
    rw [abs_mul]
    calc
      _ ≤ 4*1 := mul_le_mul (smoothTransitionDenominator_deriv_bounds x).1 ht
        (abs_nonneg _) (by norm_num)
      _ = _ := by norm_num
  have hh : |smoothTransitionDenominator x * deriv Real.smoothTransition x| ≤ 6 := by
    calc
      _ = |deriv expNegInvGlue x-deriv smoothTransitionDenominator x*Real.smoothTransition x| := by
        congr 1
        linarith [smoothTransition_product_first x]
      _ ≤ |deriv expNegInvGlue x|+|deriv smoothTransitionDenominator x*Real.smoothTransition x| := abs_sub _ _
      _ ≤ 6 := by linarith [expNegInvGlue_deriv_abs_le_two x]
  rw [abs_mul,abs_of_nonneg hD0] at hh
  nlinarith [mul_le_mul_of_nonneg_right hD (abs_nonneg (deriv Real.smoothTransition x))]

theorem smoothTransition_second_deriv_abs_le_fourteen_thousand_sixteen (x : ℝ) :
    |deriv (deriv Real.smoothTransition) x| ≤ 14016 := by
  have hD : (1/16 : ℝ) ≤ smoothTransitionDenominator x := smoothTransition_denom_lower x
  have hD0 : 0 ≤ smoothTransitionDenominator x := by linarith
  have ht : |Real.smoothTransition x| ≤ 1 := by
    rw [abs_of_nonneg (Real.smoothTransition.nonneg x)]
    exact Real.smoothTransition.le_one x
  have hprod0 : |deriv (deriv smoothTransitionDenominator) x*Real.smoothTransition x| ≤ 72 := by
    rw [abs_mul]
    calc
      _ ≤ 72*1 := mul_le_mul (smoothTransitionDenominator_deriv_bounds x).2 ht
        (abs_nonneg _) (by norm_num)
      _ = _ := by norm_num
  have hprod1 : |2*deriv smoothTransitionDenominator x*deriv Real.smoothTransition x| ≤ 768 := by
    rw [abs_mul,abs_mul]
    norm_num
    have hh := mul_le_mul (smoothTransitionDenominator_deriv_bounds x).1
      (smoothTransition_deriv_abs_le_ninety_six x) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 4)
    nlinarith
  have hh : |smoothTransitionDenominator x*deriv (deriv Real.smoothTransition) x| ≤ 876 := by
    calc
      _ = |deriv (deriv expNegInvGlue) x-
          deriv (deriv smoothTransitionDenominator) x*Real.smoothTransition x-
          2*deriv smoothTransitionDenominator x*deriv Real.smoothTransition x| := by
        congr 1
        linarith [smoothTransition_product_second x]
      _ ≤ |deriv (deriv expNegInvGlue) x|+
          |deriv (deriv smoothTransitionDenominator) x*Real.smoothTransition x|+
          |2*deriv smoothTransitionDenominator x*deriv Real.smoothTransition x| := by
        exact (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ 876 := by linarith [expNegInvGlue_second_deriv_abs_le_thirty_six x]
  rw [abs_mul,abs_of_nonneg hD0] at hh
  nlinarith [mul_le_mul_of_nonneg_right hD (abs_nonneg (deriv (deriv Real.smoothTransition) x))]

#print axioms smoothTransition_deriv_abs_le_ninety_six
#print axioms smoothTransition_second_deriv_abs_le_fourteen_thousand_sixteen
end TheoremT.Continuum
