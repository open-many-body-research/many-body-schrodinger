import HalfLineSmoothCutoff_v1

noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Set Filter
open scoped Topology
namespace TheoremT.HalfLine

theorem transition_abs_le_one (r : ℝ) : |transition r| ≤ 1 := by
  rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
  exact Real.smoothTransition.le_one _

theorem cutoff_deriv_weighted_bound {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x, |deriv transition x| ≤ C) {m r : ℝ} (hm : 0 < m) (hr : 0 < r) :
    |deriv (interiorCutoff m) r| * r ≤ C * (2+r) := by
  have h1 : |m*deriv transition (m*r-1)*transition (m-r)| * r ≤ 2*C := by
    by_cases hz : deriv transition (m*r-1) = 0
    · simp only [hz, mul_zero, zero_mul, abs_zero]
      positivity
    · have ht := transition_deriv_tsupport (subset_closure (show m*r-1 ∈ Function.support
          (deriv transition) from hz))
      have hmr : m*r ≤ 2 := by linarith [ht.2]
      have hd : |deriv transition (m*r-1)| * |transition (m-r)| ≤ C :=
        (mul_le_of_le_one_right (abs_nonneg _) (transition_abs_le_one _)).trans (hb _)
      rw [abs_mul, abs_mul, abs_of_pos hm]
      calc
        _ = (m*r) * (|deriv transition (m*r-1)| * |transition (m-r)|) := by ring
        _ ≤ 2*C := mul_le_mul hmr hd (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (by norm_num)
  have h2 : |transition (m*r-1)*deriv transition (m-r)| * r ≤ C*r := by
    rw [abs_mul]
    apply mul_le_mul_of_nonneg_right _ hr.le
    exact (mul_le_of_le_one_left (abs_nonneg _) (transition_abs_le_one _)).trans (hb _)
  rw [(interiorCutoff_hasDerivAt m r).deriv]
  calc
    _ ≤ (|m*deriv transition (m*r-1)*transition (m-r)| +
        |transition (m*r-1)*deriv transition (m-r)|) * r :=
      mul_le_mul_of_nonneg_right (abs_sub _ _) hr.le
    _ ≤ C*(2+r) := by nlinarith

theorem cutoff_eventually_one_deriv_zero {r : ℝ} (hr : 0 < r) :
    ∀ᶠ n : ℕ in atTop, interiorCutoff ((n:ℝ)+2) r = 1 ∧
      deriv (interiorCutoff ((n:ℝ)+2)) r = 0 := by
  obtain ⟨N,hN⟩ := exists_nat_gt (max (2/r) (r+1))
  filter_upwards [eventually_ge_atTop N] with n hn
  have hmn : max (2/r) (r+1) < (n:ℝ)+2 := by
    have hcast : (N:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hl : 1 < ((n:ℝ)+2)*r-1 := by
    have hdiv : 2/r < (n:ℝ)+2 := lt_of_le_of_lt (le_max_left _ _) hmn
    have hmul := (div_lt_iff₀ hr).mp hdiv
    linarith
  have hu : 1 < (n:ℝ)+2-r := by
    have hright := lt_of_le_of_lt (le_max_right _ _) hmn
    linarith
  constructor
  · simp [interiorCutoff, Real.smoothTransition.one_of_one_le hl.le,
      Real.smoothTransition.one_of_one_le hu.le]
  · rw [(interiorCutoff_hasDerivAt _ _).deriv,
      transition_deriv_zero_right hl, transition_deriv_zero_right hu]
    ring

#print axioms cutoff_deriv_weighted_bound
#print axioms cutoff_eventually_one_deriv_zero
end TheoremT.HalfLine
