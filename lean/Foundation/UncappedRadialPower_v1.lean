import CappedRadialPowerLimit_v1

/-! The actual uncapped radial power and its finite-cap approximation.
No differentiability of a nonsmooth limiting power is assumed. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal ENNReal
namespace TheoremT.Continuum

def radialPower (r : ℝ) (z : ℂ) : ℂ := (‖z‖^2 : ℝ)^r • z

theorem radialPower_continuous {r : ℝ} (hr : 0 ≤ r) : Continuous (radialPower r) :=
  ((continuous_norm.pow 2).rpow_const (fun _ => Or.inr hr)).smul continuous_id

theorem radialPower_norm {r : ℝ} (hr : 0 ≤ r) (z : ℂ) :
    ‖radialPower r z‖ = ‖z‖^(2*r+1) := by
  rw [radialPower,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (sq_nonneg ‖z‖) r)]
  rw [← Real.rpow_natCast ‖z‖ 2,← Real.rpow_mul (norm_nonneg z)]
  by_cases hz : ‖z‖ = 0
  · rw [hz,Real.zero_rpow (by linarith : 2*r+1 ≠ 0)]; simp
  · rw [Real.rpow_add (lt_of_le_of_ne (norm_nonneg z) (Ne.symm hz)),Real.rpow_one]
    norm_num

theorem zeroPowerRatio_le_square {b s : ℝ} (hb : 0 < b) (hs : 0 ≤ s) :
    smoothPowerRatio 0 b s ≤ s := by
  unfold smoothPowerRatio
  apply (div_le_iff₀ (by positivity : 0 < b+s)).mpr
  nlinarith

theorem cappedRadialPower_norm_le_power {b r : ℝ} (hb : 0 < b) (hr : 0 ≤ r) (z : ℂ) :
    ‖smoothRadialPower 0 b r z‖ ≤ ‖radialPower r z‖ := by
  simp only [smoothRadialPower,smoothRadialAmplitude,radialPower,norm_smul,Real.norm_eq_abs]
  rw [abs_of_nonneg (Real.rpow_nonneg (zeroPowerRatio_nonneg hb (sq_nonneg ‖z‖)) r),
    abs_of_nonneg (Real.rpow_nonneg (sq_nonneg ‖z‖) r)]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow
    (zeroPowerRatio_nonneg hb (sq_nonneg ‖z‖))
    (zeroPowerRatio_le_square hb (sq_nonneg ‖z‖)) hr) (norm_nonneg z)

theorem cappedRadialPower_tendsto {r : ℝ} (hr : 0 ≤ r) (z : ℂ) :
    Tendsto (fun n : ℕ => smoothRadialPower 0 ((n:ℝ)+1) r z) atTop
      (𝓝 (radialPower r z)) := by
  have hq : Tendsto (fun n : ℕ => smoothPowerRatio 0 ((n:ℝ)+1) (‖z‖^2)) atTop
      (𝓝 (‖z‖^2)) := by
    convert (tendsto_add_mul_div_add_mul_atTop_nhds
      (‖z‖^2) (1+‖z‖^2) (‖z‖^2) (d := (1:ℝ)) one_ne_zero) using 1
    · congr 1; ext n; unfold smoothPowerRatio; ring
    · simp
  exact (hq.rpow_const (Or.inr hr)).smul_const z

theorem radialPower_eLpNorm {N : ℕ} {r : ℝ} (hr : 0 ≤ r)
    (f : SpatialL2 N) (q : ℝ≥0∞) :
    eLpNorm (fun x => radialPower r (f x)) q volume =
      (eLpNorm f (q*ENNReal.ofReal (2*r+1)) volume)^(2*r+1) := by
  rw [← eLpNorm_norm_rpow (f : Configuration N → ℂ) (by linarith : 0 < 2*r+1)]
  apply eLpNorm_congr_norm_ae
  filter_upwards with x
  rw [radialPower_norm hr,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (norm_nonneg (f x)) (2*r+1))]

#print axioms radialPower_eLpNorm
#print axioms cappedRadialPower_tendsto
end TheoremT.Continuum
