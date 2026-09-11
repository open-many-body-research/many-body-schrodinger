import EuclideanOscillatorOperator_v1

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace TheoremT.Continuum
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem compact_euclidean_oscillator_norm_lower {u : EuclideanSpace ℝ ι → ℂ}
    (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) (a : ℝ)
    (hf : MemLp u 2 volume) (hA : MemLp (euclideanOscillator a u) 2 volume) :
    (Fintype.card ι : ℝ)*a*‖hf.toLp u‖ ≤ ‖hA.toLp (euclideanOscillator a u)‖ := by
  have he := compact_euclidean_oscillator_form_bound (hu.of_le (by simp)) hc a
  change _ ≤ (∫ x,∑ k : ι,‖oscillatorPartial u k x‖^2)+_ at he
  rw [← compact_euclidean_oscillator_energy a hu hc,← actual_l2_toLp_norm_sq_integral hf] at he
  have hab := actual_l2_integral_inner_abs_le hf hA
  have hb := he.trans ((le_abs_self _).trans hab)
  by_cases hz : ‖hf.toLp u‖=0
  · simp only [hz,mul_zero]
    exact norm_nonneg _
  · have hp := lt_of_le_of_ne (norm_nonneg (hf.toLp u)) (Ne.symm hz)
    have hh : ((Fintype.card ι : ℝ)*a*‖hf.toLp u‖)*‖hf.toLp u‖ ≤
        ‖hA.toLp (euclideanOscillator a u)‖*‖hf.toLp u‖ := by nlinarith only [hb]
    exact (mul_le_mul_iff_left₀ hp).mp hh

theorem compact_euclidean_oscillator_integral_lower {u : EuclideanSpace ℝ ι → ℂ}
    (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) {a : ℝ} (ha : 0 ≤ a) :
    ((Fintype.card ι : ℝ)*a)^2*(∫ x,‖u x‖^2) ≤ ∫ x,‖euclideanOscillator a u x‖^2 := by
  have hf : MemLp u 2 volume := hu.continuous.memLp_of_hasCompactSupport hc
  have hA : MemLp (euclideanOscillator a u) 2 volume :=
    (euclideanOscillator_contDiff a hu).continuous.memLp_of_hasCompactSupport (euclideanOscillator_compact a hc)
  have h := compact_euclidean_oscillator_norm_lower hu hc a hf hA
  have hp : 0 ≤ (Fintype.card ι : ℝ)*a*‖hf.toLp u‖ := by positivity
  have hs := pow_le_pow_left₀ hp h 2
  simpa only [mul_pow,actual_l2_toLp_norm_sq_integral] using hs

#print axioms compact_euclidean_oscillator_norm_lower
#print axioms compact_euclidean_oscillator_integral_lower
end TheoremT.Continuum
