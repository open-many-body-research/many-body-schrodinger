import CappedRadialPower_v1
import CoulombSmoothPowerSobolev_v1
import LpLimitBound_v1

/-! Remove positive regularization in actual L2 and retain the uniform critical
Sobolev estimate. The finite cap remains; no derivative of the limiting map is
silently asserted or needed in the lower-semicontinuity step. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal ENNReal
namespace TheoremT.Continuum

theorem smoothRadialPower_norm_le_cap {a b r : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hr : 0 ≤ r) (z : ℂ) :
    ‖smoothRadialPower a b r z‖ ≤ b^r*‖z‖ := by
  rw [smoothRadialPower,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (smoothRadialAmplitude_pos ha hab z).le]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow (smoothPowerRatio_pos ha hab (sq_nonneg ‖z‖)).le
      (smoothPowerRatio_le_cap ha hab (sq_nonneg ‖z‖)) hr) (norm_nonneg z)

theorem smoothRadialPowerL2_tendsto_zero_regularization {N : ℕ} {a : ℕ → ℝ} {b r : ℝ}
    (hb : 0 < b) (hr : 0 ≤ r) (ha : ∀ n, 0 < a n) (hab : ∀ n, a n ≤ b)
    (ht : Tendsto a atTop (𝓝 0)) (f : SpatialL2 N) :
    Tendsto (fun n => smoothRadialPowerL2 (ha n) (hab n) hr f) atTop
      (𝓝 (cappedRadialPowerL2 hb hr f)) := by
  have hc : 0 ≤ b^r := Real.rpow_nonneg hb.le r
  apply configuration_L2_tendsto_dominated _ _ (fun x => b^r*‖f x‖)
  · simpa only [Pi.smul_def,smul_eq_mul] using (Lp.memLp f).norm.const_smul (b^r)
  · intro n
    filter_upwards [smoothRadialPowerL2_ae (ha n) (hab n) hr f] with x hx
    rw [hx,Real.norm_eq_abs,abs_mul,abs_of_nonneg hc,abs_norm]
    exact smoothRadialPower_norm_le_cap (ha n) (hab n) hr (f x)
  · filter_upwards [cappedRadialPowerL2_ae hb hr f] with x hx
    rw [hx,Real.norm_eq_abs,abs_mul,abs_of_nonneg hc,abs_norm]
    exact cappedRadialPower_norm_le hb hr (f x)
  · have hseq : ∀ᵐ x, ∀ n, smoothRadialPowerL2 (ha n) (hab n) hr f x =
        smoothRadialPower (a n) b r (f x) := by
      rw [ae_all_iff]
      exact fun n => smoothRadialPowerL2_ae (ha n) (hab n) hr f
    filter_upwards [hseq,cappedRadialPowerL2_ae hb hr f] with x hx hx0
    simp_rw [hx,hx0]
    exact smoothRadialPower_tendsto_zero_regularization hr ht (f x)

theorem scalar_eigen_capped_power_sobolev {N : ℕ} (hN : 0 < N)
    {Z E b r : ℝ} {f : SpatialL2 N} (hg : scalarHamiltonianGraph N Z f ((E : ℂ) • f))
    (hb : 0 < b) (hr : 0 ≤ r) :
    eLpNorm (cappedRadialPowerL2 hb hr f) (atomicSobolevExponent N) volume ≤
      ENNReal.ofReal (smoothPowerSobolevCoefficient N Z E r*‖cappedRadialPowerL2 hb hr f‖) := by
  let a : ℕ → ℝ := fun n => b/((n : ℝ)+1)
  have ha (n : ℕ) : 0 < a n := by dsimp [a]; positivity
  have hab (n : ℕ) : a n ≤ b := by
    dsimp [a]
    apply (div_le_iff₀ (by positivity : 0 < (n : ℝ)+1)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have ht : Tendsto a atTop (𝓝 0) := by
    simpa only [a,div_eq_mul_inv,mul_zero,one_mul,one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul b
  have hl := smoothRadialPowerL2_tendsto_zero_regularization hb hr ha hab ht f
  apply eLpNorm_le_of_L2_tendsto_bound _ hl
    (fun n => smoothPowerSobolevCoefficient N Z E r*‖smoothRadialPowerL2 (ha n) (hab n) hr f‖)
    (tendsto_const_nhds.mul hl.norm)
  exact fun n => scalar_eigen_smooth_power_sobolev hN hg (ha n) (hab n) hr

#print axioms smoothRadialPowerL2_tendsto_zero_regularization
#print axioms scalar_eigen_capped_power_sobolev
end TheoremT.Continuum
