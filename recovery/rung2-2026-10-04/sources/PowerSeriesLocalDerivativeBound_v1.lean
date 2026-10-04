import PowerSeriesCenterDerivativeBound_v1
import PowerSeriesUniformTranslationBound_v1

/-! Local all-order derivative bounds with constants before the point and order.
A single summable translated-series majorant and the actual permutation norm
estimate produce this bound. Finite-order smooth compactness is not used.
-/
noncomputable section
open scoped BigOperators ENNReal NNReal
namespace TheoremT.Continuum

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {f : E → F} {p : FormalMultilinearSeries ℝ E F} {x : E} {R : ℝ≥0∞}

theorem powerSeries_local_factorial_radius_bound
    (hf : HasFPowerSeriesOnBall f p x R) {r s : ℝ≥0}
    (hs : 0 < s) (hrs : (r+s : ℝ≥0∞) < R) :
    ∃ C > 0, ∀ z : E, ‖z‖₊ ≤ r → ∀ k : ℕ,
      ‖iteratedFDeriv ℝ k f (x+z)‖ ≤ (k.factorial : ℝ) * (C / (s : ℝ)^k) := by
  obtain ⟨C,hC,hbound⟩ :=
    powerSeries_changeOrigin_uniform_geometric_bound p hs (hrs.trans_le hf.r_le)
  refine ⟨C,hC,?_⟩
  intro z hz k
  have hzR : (‖z‖₊ : ℝ≥0∞) < R :=
    (ENNReal.coe_le_coe.mpr hz).trans_lt
      ((le_add_of_nonneg_right (by positivity)).trans_lt hrs)
  exact (powerSeries_norm_iteratedFDeriv_le_factorial_coeff (hf.changeOrigin hzR) k).trans
    (mul_le_mul_of_nonneg_left (hbound z hz k) (Nat.cast_nonneg _))

theorem analyticAt_local_factorial_bound (hf : AnalyticAt ℝ f x) :
    ∃ rho > 0, ∃ C > 0, ∃ A > 0, ∀ y : E, y ∈ Metric.ball x rho → ∀ k : ℕ,
      ‖iteratedFDeriv ℝ k f y‖ ≤ C * A^k * (k.factorial : ℝ) := by
  obtain ⟨p,R,hp⟩ := hf
  obtain ⟨t,ht0,htR⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp.r_pos
  have ht : 0 < t := by exact_mod_cast ht0
  let r : ℝ≥0 := t/2
  have hr : 0 < r := half_pos ht
  have hsum : r+r = t := add_halves t
  have hrs : (r+r : ℝ≥0∞) < R := by
    rw [← ENNReal.coe_add, hsum]
    exact htR
  obtain ⟨C,hC,hbound⟩ := powerSeries_local_factorial_radius_bound hp hr hrs
  refine ⟨(r : ℝ),hr,C,hC,(r : ℝ)⁻¹,inv_pos.mpr hr,?_⟩
  intro y hy k
  have hyr : ‖y-x‖₊ ≤ r := by
    have hnorm : ‖y-x‖ < (r : ℝ) := by simpa only [Metric.mem_ball, dist_eq_norm] using hy
    exact_mod_cast hnorm.le
  have hb := hbound (y-x) hyr k
  have hxy : x+(y-x) = y := by abel
  simpa only [hxy, div_eq_mul_inv, inv_pow, mul_comm, mul_left_comm, mul_assoc] using hb

end TheoremT.Continuum
