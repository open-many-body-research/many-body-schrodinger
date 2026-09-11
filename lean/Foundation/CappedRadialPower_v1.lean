import SmoothRadialPowerL2_v1
import ConfigurationLpDominated_v1

/-! Remove the positive regularization while retaining a finite radial cap.
The zero-regularization map is used only as a continuous L2 map here; no
unproved classical derivative at zero is used. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace TheoremT.Continuum

theorem zeroPowerRatio_nonneg {b s : ℝ} (hb : 0 < b) (hs : 0 ≤ s) :
    0 ≤ smoothPowerRatio 0 b s := by unfold smoothPowerRatio; positivity

theorem zeroPowerRatio_le_cap {b s : ℝ} (hb : 0 < b) (hs : 0 ≤ s) :
    smoothPowerRatio 0 b s ≤ b := by
  unfold smoothPowerRatio
  apply (div_le_iff₀ (by positivity : 0 < b+s)).mpr
  nlinarith

theorem cappedRadialPower_continuous {b r : ℝ} (hb : 0 < b) (hr : 0 ≤ r) :
    Continuous (smoothRadialPower 0 b r) := by
  have hq : Continuous (fun z : ℂ => smoothPowerRatio 0 b (‖z‖^2)) := by
    unfold smoothPowerRatio
    exact (continuous_const.mul (continuous_const.add (continuous_norm.pow 2))).div
      (continuous_const.add (continuous_norm.pow 2)) (fun z => by positivity)
  exact (hq.rpow_const (fun z => Or.inr hr)).smul continuous_id

theorem cappedRadialPower_norm_le {b r : ℝ} (hb : 0 < b) (hr : 0 ≤ r) (z : ℂ) :
    ‖smoothRadialPower 0 b r z‖ ≤ b^r*‖z‖ := by
  have hn := Real.rpow_nonneg (zeroPowerRatio_nonneg hb (sq_nonneg ‖z‖)) r
  rw [smoothRadialPower,smoothRadialAmplitude,norm_smul,Real.norm_eq_abs,abs_of_nonneg hn]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow (zeroPowerRatio_nonneg hb (sq_nonneg ‖z‖))
      (zeroPowerRatio_le_cap hb (sq_nonneg ‖z‖)) hr) (norm_nonneg z)

theorem cappedRadialPower_memLp {N : ℕ} {b r : ℝ} (hb : 0 < b) (hr : 0 ≤ r) (f : SpatialL2 N) :
    MemLp (fun x => smoothRadialPower 0 b r (f x)) 2 volume :=
  (Lp.memLp f).of_le_mul ((cappedRadialPower_continuous hb hr).comp_aestronglyMeasurable
    (Lp.aestronglyMeasurable f)) (Eventually.of_forall (fun x => cappedRadialPower_norm_le hb hr (f x)))

def cappedRadialPowerL2 {N : ℕ} {b r : ℝ} (hb : 0 < b) (hr : 0 ≤ r) (f : SpatialL2 N) : SpatialL2 N :=
  (cappedRadialPower_memLp hb hr f).toLp (fun x => smoothRadialPower 0 b r (f x))

theorem cappedRadialPowerL2_ae {N : ℕ} {b r : ℝ} (hb : 0 < b) (hr : 0 ≤ r) (f : SpatialL2 N) :
    cappedRadialPowerL2 hb hr f =ᵐ[volume] (fun x => smoothRadialPower 0 b r (f x)) :=
  MemLp.coeFn_toLp _

theorem smoothRadialPower_tendsto_zero_regularization {a : ℕ → ℝ} {b r : ℝ}
    (hr : 0 ≤ r) (ha : Tendsto a atTop (𝓝 0)) (z : ℂ) :
    Tendsto (fun n => smoothRadialPower (a n) b r z) atTop (𝓝 (smoothRadialPower 0 b r z)) := by
  have hq := ((ha.add_const (‖z‖^2)).const_mul b).div_const (b+‖z‖^2)
  exact (hq.rpow_const (Or.inr hr)).smul_const z

#print axioms cappedRadialPower_memLp
#print axioms smoothRadialPower_tendsto_zero_regularization
end TheoremT.Continuum
