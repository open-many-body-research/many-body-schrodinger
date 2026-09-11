import HalfLineCompactPairing_v1
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Normed.Group.Bounded

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace TheoremT.HalfLine

abbrev transition := Real.smoothTransition

theorem transition_deriv_zero_left {r : ℝ} (hr : r < 0) : deriv transition r = 0 := by
  have he : transition =ᶠ[𝓝 r] fun _ => (0:ℝ) := by
    filter_upwards [Iio_mem_nhds hr] with x hx
    exact Real.smoothTransition.zero_of_nonpos hx.le
  simpa using he.deriv_eq

theorem transition_deriv_zero_right {r : ℝ} (hr : 1 < r) : deriv transition r = 0 := by
  have he : transition =ᶠ[𝓝 r] fun _ => (1:ℝ) := by
    filter_upwards [Ioi_mem_nhds hr] with x hx
    exact Real.smoothTransition.one_of_one_le hx.le
  simpa using he.deriv_eq

theorem transition_deriv_tsupport : tsupport (deriv transition) ⊆ Icc (0:ℝ) 1 := by
  apply closure_minimal _ isClosed_Icc
  intro r hr
  change deriv transition r ≠ 0 at hr
  constructor
  · by_contra hn
    exact hr (transition_deriv_zero_left (lt_of_not_ge hn))
  · by_contra hn
    exact hr (transition_deriv_zero_right (lt_of_not_ge hn))

theorem transition_deriv_compact : HasCompactSupport (deriv transition) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) transition_deriv_tsupport

theorem transition_deriv_bounded : ∃ C : ℝ, 0 ≤ C ∧ ∀ r, |deriv transition r| ≤ C := by
  obtain ⟨C,hC⟩ := transition_deriv_compact.exists_bound_of_continuous
    ((Real.smoothTransition.contDiff : ContDiff ℝ ∞ transition).continuous_deriv (by simp))
  refine ⟨max C 0, le_max_right _ _, fun r => ?_⟩
  exact (show |deriv transition r| ≤ C from hC r).trans (le_max_left _ _)

def interiorCutoff (m r : ℝ) : ℝ := transition (m*r-1)*transition (m-r)

theorem interiorCutoff_contDiff (m : ℝ) : ContDiff ℝ ∞ (interiorCutoff m) :=
  (Real.smoothTransition.contDiff.comp (contDiff_const.mul contDiff_id |>.sub contDiff_const)).mul
    (Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id))

theorem interiorCutoff_nonneg (m r : ℝ) : 0 ≤ interiorCutoff m r :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem interiorCutoff_le_one (m r : ℝ) : interiorCutoff m r ≤ 1 := by
  exact mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.le_one _)

theorem interiorCutoff_tsupport {m : ℝ} (hm : 0 < m) :
    tsupport (interiorCutoff m) ⊆ Icc m⁻¹ m := by
  apply closure_minimal _ isClosed_Icc
  intro r hr
  change interiorCutoff m r ≠ 0 at hr
  have hl : ¬ m*r-1 ≤ 0 := by
    intro h
    exact hr (by simp [interiorCutoff, Real.smoothTransition.zero_of_nonpos h])
  have hu : ¬ m-r ≤ 0 := by
    intro h
    exact hr (by simp [interiorCutoff, Real.smoothTransition.zero_of_nonpos h])
  constructor
  · rw [inv_eq_one_div]
    apply (div_le_iff₀ hm).mpr
    nlinarith
  · linarith

theorem interiorCutoff_compact {m : ℝ} (hm : 0 < m) : HasCompactSupport (interiorCutoff m) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (interiorCutoff_tsupport hm)

theorem interiorCutoff_positive_support {m : ℝ} (hm : 0 < m) :
    tsupport (interiorCutoff m) ⊆ Ioi (0:ℝ) := by
  intro r hr
  exact lt_of_lt_of_le (inv_pos.mpr hm) ((interiorCutoff_tsupport hm hr).1)

theorem interiorCutoff_hasDerivAt (m r : ℝ) : HasDerivAt (interiorCutoff m)
    (m*deriv transition (m*r-1)*transition (m-r) -
      transition (m*r-1)*deriv transition (m-r)) r := by
  have ht (x : ℝ) := (Real.smoothTransition.contDiff : ContDiff ℝ ∞ transition).differentiable
    (by simp) x |>.hasDerivAt
  have h1 := (ht (m*r-1)).comp r (((hasDerivAt_id r).const_mul m).sub_const 1)
  have h2 := (ht (m-r)).comp r ((hasDerivAt_const r m).sub (hasDerivAt_id r))
  convert! h1.mul h2 using 1 <;>
    simp only [interiorCutoff, Function.comp_apply, id_eq, mul_one, zero_sub, mul_neg_one] <;> ring

#print axioms transition_deriv_bounded
#print axioms interiorCutoff_tsupport
#print axioms interiorCutoff_hasDerivAt
end TheoremT.HalfLine
