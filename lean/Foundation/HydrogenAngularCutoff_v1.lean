import PolarThree_v1
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! A concrete nonnegative radial cutoff for angular integration identities.
The scalar bump is centered at 1 with inner radius 1/4 and outer radius 1/2.
Its composition with squared Euclidean radius is smooth and supported away
from zero. The radial cancellation constant is proved strictly positive. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace TheoremT.HydrogenPolynomial

def angularCutoffBump : ContDiffBump (1 : ℝ) :=
  ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

def angularCutoff (t : ℝ) : ℝ := angularCutoffBump t

theorem angularCutoff_contDiff : ContDiff ℝ ∞ angularCutoff := angularCutoffBump.contDiff

theorem angularCutoff_nonneg (t : ℝ) : 0 ≤ angularCutoff t := angularCutoffBump.nonneg

theorem angularCutoff_le_one (t : ℝ) : angularCutoff t ≤ 1 := angularCutoffBump.le_one

theorem angularCutoff_eq_one {t : ℝ} (ht : |t - 1| ≤ 1 / 4) : angularCutoff t = 1 := by
  apply angularCutoffBump.one_of_mem_closedBall
  simpa only [Metric.mem_closedBall, Real.dist_eq, angularCutoffBump] using ht

theorem angularCutoff_eq_zero_of_le {t : ℝ} (ht : t ≤ 1 / 2) : angularCutoff t = 0 := by
  apply angularCutoffBump.zero_of_le_dist
  change (1 / 2 : ℝ) ≤ dist t 1
  rw [Real.dist_eq, abs_of_nonpos (by linarith : t - 1 ≤ 0)]
  linarith

theorem angularCutoff_eq_zero_of_ge {t : ℝ} (ht : 3 / 2 ≤ t) : angularCutoff t = 0 := by
  apply angularCutoffBump.zero_of_le_dist
  change (1 / 2 : ℝ) ≤ dist t 1
  rw [Real.dist_eq, abs_of_nonneg (by linarith : 0 ≤ t - 1)]
  linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem angularCutoff_norm_sq_contDiff :
    ContDiff ℝ ∞ (fun x : E => angularCutoff (‖x‖ ^ 2)) :=
  angularCutoff_contDiff.comp (contDiff_norm_sq ℝ)

theorem angularCutoff_norm_sq_support :
    tsupport (fun x : E => angularCutoff (‖x‖ ^ 2)) ⊆
      {x : E | 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 2} := by
  apply closure_minimal
  · intro x hx
    constructor
    · by_contra hn
      have hn' : ‖x‖ < 1 / 2 := lt_of_not_ge hn
      exact hx (angularCutoff_eq_zero_of_le (by nlinarith [norm_nonneg x]))
    · by_contra hn
      have hn' : 2 < ‖x‖ := lt_of_not_ge hn
      exact hx (angularCutoff_eq_zero_of_ge (by nlinarith [norm_nonneg x]))
  · exact (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)

theorem angularCutoff_norm_sq_zero_not_tsupport :
    (0 : E) ∉ tsupport (fun x : E => angularCutoff (‖x‖ ^ 2)) := by
  intro h
  have hz := (angularCutoff_norm_sq_support h).1
  norm_num at hz

variable [FiniteDimensional ℝ E]

theorem angularCutoff_norm_sq_compact :
    HasCompactSupport (fun x : E => angularCutoff (‖x‖ ^ 2)) := by
  apply (isCompact_closedBall (0 : E) 2).of_isClosed_subset (isClosed_tsupport _)
  intro x hx
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    (angularCutoff_norm_sq_support hx).2

theorem angularCutoff_square_compact :
    HasCompactSupport (fun r : ℝ => angularCutoff (r ^ 2)) := by
  simpa only [Real.norm_eq_abs, sq_abs] using (angularCutoff_norm_sq_compact (E := ℝ))

theorem angularCutoff_square_integrable :
    Integrable (fun r : ℝ => angularCutoff (r ^ 2)) :=
  (angularCutoff_contDiff.continuous.comp (continuous_id.pow 2)).integrable_of_hasCompactSupport
    angularCutoff_square_compact

theorem angularCutoff_square_one_on_interval {r : ℝ} (hr : r ∈ Ioo 1 (17 / 16)) :
    angularCutoff (r ^ 2) = 1 := by
  apply angularCutoff_eq_one
  rw [abs_le]
  constructor <;> nlinarith [hr.1, hr.2]

theorem angularCutoff_radial_integral_pos :
    0 < ∫ r : ℝ in Ioi 0, angularCutoff (r ^ 2) := by
  apply (integral_pos_iff_support_of_nonneg
    (fun r : ℝ => angularCutoff_nonneg (r ^ 2))
    angularCutoff_square_integrable.restrict).2
  have hs : Ioo (1 : ℝ) (17 / 16) ⊆ Function.support
      (fun r : ℝ => angularCutoff (r ^ 2)) := by
    intro r hr
    rw [Function.mem_support, angularCutoff_square_one_on_interval hr]
    norm_num
  have hm : 0 < (volume.restrict (Ioi (0 : ℝ))) (Ioo 1 (17 / 16)) := by
    rw [Measure.restrict_apply measurableSet_Ioo]
    have he : Ioo (1 : ℝ) (17 / 16) ∩ Ioi 0 = Ioo 1 (17 / 16) := by
      apply inter_eq_left.mpr
      intro r hr
      exact lt_trans zero_lt_one hr.1
    rw [he, Real.volume_Ioo]
    norm_num
  exact hm.trans_le (measure_mono hs)

#print axioms angularCutoff_contDiff
#print axioms angularCutoff_norm_sq_support
#print axioms angularCutoff_norm_sq_zero_not_tsupport
#print axioms angularCutoff_norm_sq_compact
#print axioms angularCutoff_radial_integral_pos
end TheoremT.HydrogenPolynomial
