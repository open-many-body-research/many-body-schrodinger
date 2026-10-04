import HalfLineSmoothCutoff_v1
import Mathlib.Analysis.Calculus.Deriv.Support

/-!
Actual scalar smooth interval windows with additive-gap derivative bounds.
The fixed derivative constants for Real.smoothTransition are proved finite;
no numerical value or effective computation of those constants is claimed.
-/
noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace TheoremT.Continuum

theorem smoothTransition_derivative_bounds :
    ∃ C1 C2 : ℝ, 0 ≤ C1 ∧ 0 ≤ C2 ∧
      (∀ x, |deriv Real.smoothTransition x| ≤ C1) ∧
      ∀ x, |deriv (deriv Real.smoothTransition) x| ≤ C2 := by
  obtain ⟨C1, hC1, hb1⟩ := TheoremT.HalfLine.transition_deriv_bounded
  have hc2 : HasCompactSupport (deriv (deriv Real.smoothTransition)) :=
    TheoremT.HalfLine.transition_deriv_compact.deriv
  have hd : ContDiff ℝ ∞ (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff : ContDiff ℝ ∞ Real.smoothTransition).deriv'
  obtain ⟨C2, hb2⟩ := hc2.exists_bound_of_continuous (hd.continuous_deriv (by simp))
  refine ⟨C1, max C2 0, hC1, le_max_right _ _, hb1, fun x => ?_⟩
  exact (show |deriv (deriv Real.smoothTransition) x| ≤ C2 from hb2 x).trans (le_max_left _ _)

def transitionWindow (r R x : ℝ) : ℝ :=
  Real.smoothTransition ((x + R) / (R - r)) * Real.smoothTransition ((R - x) / (R - r))

theorem transitionWindow_contDiff (r R : ℝ) : ContDiff ℝ ∞ (transitionWindow r R) := by
  unfold transitionWindow
  fun_prop

theorem transitionWindow_nonneg (r R x : ℝ) : 0 ≤ transitionWindow r R x :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem transitionWindow_le_one (r R x : ℝ) : transitionWindow r R x ≤ 1 :=
  (mul_le_mul (Real.smoothTransition.le_one _) (Real.smoothTransition.le_one _)
    (Real.smoothTransition.nonneg _) (by norm_num)).trans_eq (one_mul _)

theorem transitionWindow_plateau {r R : ℝ} (hgap : r < R)
    {x : ℝ} (hx : x ∈ Icc (-r) r) : transitionWindow r R x = 1 := by
  have hleft : 1 ≤ (x + R) / (R - r) := (le_div_iff₀ (sub_pos.mpr hgap)).mpr (by linarith [hx.1])
  have hright : 1 ≤ (R - x) / (R - r) := (le_div_iff₀ (sub_pos.mpr hgap)).mpr (by linarith [hx.2])
  simp only [transitionWindow, Real.smoothTransition.one_of_one_le hleft,
    Real.smoothTransition.one_of_one_le hright, mul_one]

theorem transitionWindow_tsupport {r R : ℝ} (hgap : r < R) :
    tsupport (transitionWindow r R) ⊆ Icc (-R) R := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  change transitionWindow r R x ≠ 0 at hx
  constructor
  · by_contra hn
    have hz : (x + R) / (R - r) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) (sub_nonneg.mpr hgap.le)
    exact hx (by simp [transitionWindow, Real.smoothTransition.zero_of_nonpos hz])
  · by_contra hn
    have hz : (R - x) / (R - r) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) (sub_nonneg.mpr hgap.le)
    exact hx (by simp [transitionWindow, Real.smoothTransition.zero_of_nonpos hz])

theorem transitionWindow_compact {r R : ℝ} (hgap : r < R) :
    HasCompactSupport (transitionWindow r R) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (transitionWindow_tsupport hgap)

theorem transitionWindow_first (r R x : ℝ) : deriv (transitionWindow r R) x =
    (deriv Real.smoothTransition ((x + R) / (R - r)) *
        Real.smoothTransition ((R - x) / (R - r)) -
      Real.smoothTransition ((x + R) / (R - r)) *
        deriv Real.smoothTransition ((R - x) / (R - r))) / (R - r) := by
  have ht (z : ℝ) := (Real.smoothTransition.contDiff : ContDiff ℝ ∞ Real.smoothTransition).differentiable
    (by simp) z |>.hasDerivAt
  have h1 := (ht ((x + R) / (R - r))).comp x (((hasDerivAt_id x).add_const R).div_const (R - r))
  have h2 := (ht ((R - x) / (R - r))).comp x
    (((hasDerivAt_const x R).sub (hasDerivAt_id x)).div_const (R - r))
  have hh := (h1.mul h2).deriv
  change deriv (transitionWindow r R) x = _ at hh
  rw [hh]
  simp only [Function.comp_apply, Pi.sub_apply, id_eq, zero_sub, div_eq_mul_inv]
  ring

theorem transitionWindow_second (r R x : ℝ) : deriv (deriv (transitionWindow r R)) x =
    (deriv (deriv Real.smoothTransition) ((x + R) / (R - r)) *
        Real.smoothTransition ((R - x) / (R - r)) -
      2 * deriv Real.smoothTransition ((x + R) / (R - r)) *
        deriv Real.smoothTransition ((R - x) / (R - r)) +
      Real.smoothTransition ((x + R) / (R - r)) *
        deriv (deriv Real.smoothTransition) ((R - x) / (R - r))) / (R - r) ^ 2 := by
  have ht (z : ℝ) := (Real.smoothTransition.contDiff : ContDiff ℝ ∞ Real.smoothTransition).differentiable
    (by simp) z |>.hasDerivAt
  have htd : ContDiff ℝ ∞ (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff : ContDiff ℝ ∞ Real.smoothTransition).deriv'
  have hdt (z : ℝ) := htd.differentiable (by simp) z |>.hasDerivAt
  have ha := ((hasDerivAt_id x).add_const R).div_const (R - r)
  have hb := ((hasDerivAt_const x R).sub (hasDerivAt_id x)).div_const (R - r)
  have h1 := (ht ((x + R) / (R - r))).comp x ha
  have h2 := (ht ((R - x) / (R - r))).comp x hb
  have h1d := (hdt ((x + R) / (R - r))).comp x ha
  have h2d := (hdt ((R - x) / (R - r))).comp x hb
  have hh := (((h1d.mul h2).sub (h1.mul h2d)).div_const (R - r)).deriv
  have he := funext (transitionWindow_first r R)
  rw [he]
  change deriv (fun x =>
    (deriv Real.smoothTransition ((x + R) / (R - r)) *
        Real.smoothTransition ((R - x) / (R - r)) -
      Real.smoothTransition ((x + R) / (R - r)) *
        deriv Real.smoothTransition ((R - x) / (R - r))) / (R - r)) x = _ at hh
  rw [hh]
  simp only [Function.comp_apply, Pi.sub_apply, id_eq, zero_sub, div_eq_mul_inv, ← inv_pow]
  ring

theorem transitionWindow_first_bound {C1 r R : ℝ}
    (hC1 : ∀ x, |deriv Real.smoothTransition x| ≤ C1)
    (hgap : r < R) (x : ℝ) : |deriv (transitionWindow r R) x| ≤ 2 * C1 / (R - r) := by
  have hC10 : 0 ≤ C1 := (abs_nonneg _).trans (hC1 0)
  have hT (z : ℝ) : |Real.smoothTransition z| ≤ 1 := by
    rw [abs_of_nonneg (Real.smoothTransition.nonneg z)]
    exact Real.smoothTransition.le_one z
  have ha : |deriv Real.smoothTransition ((x + R) / (R - r)) *
      Real.smoothTransition ((R - x) / (R - r))| ≤ C1 := by
    rw [abs_mul]
    exact (mul_le_mul (hC1 _) (hT _) (abs_nonneg _) hC10).trans_eq (mul_one _)
  have hb : |Real.smoothTransition ((x + R) / (R - r)) *
      deriv Real.smoothTransition ((R - x) / (R - r))| ≤ C1 := by
    rw [abs_mul]
    exact (mul_le_mul (hT _) (hC1 _) (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  rw [transitionWindow_first, abs_div, abs_of_pos (sub_pos.mpr hgap)]
  apply div_le_div_of_nonneg_right _ (sub_nonneg.mpr hgap.le)
  have ha' := abs_le.mp ha
  have hb' := abs_le.mp hb
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem transitionWindow_second_bound {C1 C2 r R : ℝ}
    (hC1 : ∀ x, |deriv Real.smoothTransition x| ≤ C1)
    (hC2 : ∀ x, |deriv (deriv Real.smoothTransition) x| ≤ C2)
    (hgap : r < R) (x : ℝ) :
    |deriv (deriv (transitionWindow r R)) x| ≤ 2 * (C2 + C1 ^ 2) / (R - r) ^ 2 := by
  have hC10 : 0 ≤ C1 := (abs_nonneg _).trans (hC1 0)
  have hC20 : 0 ≤ C2 := (abs_nonneg _).trans (hC2 0)
  have hT (z : ℝ) : |Real.smoothTransition z| ≤ 1 := by
    rw [abs_of_nonneg (Real.smoothTransition.nonneg z)]
    exact Real.smoothTransition.le_one z
  have ha : |deriv (deriv Real.smoothTransition) ((x + R) / (R - r)) *
      Real.smoothTransition ((R - x) / (R - r))| ≤ C2 := by
    rw [abs_mul]
    exact (mul_le_mul (hC2 _) (hT _) (abs_nonneg _) hC20).trans_eq (mul_one _)
  have hb : |deriv Real.smoothTransition ((x + R) / (R - r)) *
      deriv Real.smoothTransition ((R - x) / (R - r))| ≤ C1 ^ 2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul (hC1 _) (hC1 _) (abs_nonneg _) hC10
  have hc : |Real.smoothTransition ((x + R) / (R - r)) *
      deriv (deriv Real.smoothTransition) ((R - x) / (R - r))| ≤ C2 := by
    rw [abs_mul]
    exact (mul_le_mul (hT _) (hC2 _) (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hden : 0 ≤ (R - r) ^ 2 := (pow_pos (sub_pos.mpr hgap) 2).le
  rw [transitionWindow_second, abs_div, abs_of_nonneg hden]
  apply div_le_div_of_nonneg_right _ hden
  have ha' := abs_le.mp ha
  have hb' := abs_le.mp hb
  have hc' := abs_le.mp hc
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

#print axioms smoothTransition_derivative_bounds
#print axioms transitionWindow_contDiff
#print axioms transitionWindow_nonneg
#print axioms transitionWindow_le_one
#print axioms transitionWindow_plateau
#print axioms transitionWindow_tsupport
#print axioms transitionWindow_compact
#print axioms transitionWindow_first
#print axioms transitionWindow_second
#print axioms transitionWindow_first_bound
#print axioms transitionWindow_second_bound

end TheoremT.Continuum
