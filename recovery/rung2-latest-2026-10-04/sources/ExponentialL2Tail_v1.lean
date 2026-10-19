import ExponentialWeightComparison_v1
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-! Exact exponential L² tail estimate on physical configuration space from
an actual exponentially weighted L² function. The prefactor is its actual
weighted norm; no algorithm for evaluating that norm is asserted. -/
noncomputable section
open MeasureTheory Filter
namespace TheoremT.Continuum

def exteriorL2 {N : ℕ} (r : ℝ) (f : SpatialL2 N) : SpatialL2 N :=
  (MemLp.indicator (measurableSet_le measurable_const continuous_norm.measurable)
    (Lp.memLp f)).toLp ({x : Configuration N | r ≤ ‖x‖}.indicator (fun x => f x))

theorem exteriorL2_ae {N : ℕ} (r : ℝ) (f : SpatialL2 N) :
    exteriorL2 r f =ᵐ[volume] ({x : Configuration N | r ≤ ‖x‖}.indicator (fun x => f x)) :=
  MemLp.coeFn_toLp _

theorem exponential_L2_tail_bound {N : ℕ} {a : ℝ} (ha : 0 ≤ a)
    (f : SpatialL2 N) (hw : MemLp (fun x => Real.exp (a*‖x‖) • f x) 2 volume)
    (r : ℝ) :
    ‖exteriorL2 r f‖ ≤ Real.exp (-a*r) *
      ‖hw.toLp (fun x => Real.exp (a*‖x‖) • f x)‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [exteriorL2_ae r f,hw.coeFn_toLp] with x hx hy
  rw [hx,hy]
  by_cases hr : r ≤ ‖x‖
  · rw [Set.indicator_of_mem (show x ∈ {x : Configuration N | r ≤ ‖x‖} from hr)]
    simp only [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    rw [← mul_assoc,← Real.exp_add]
    have h : (1 : ℝ) ≤ Real.exp (-a*r+a*‖x‖) :=
      Real.one_le_exp_iff.mpr (by nlinarith [mul_nonneg ha (sub_nonneg.mpr hr)])
    simpa only [one_mul] using mul_le_mul_of_nonneg_right h (norm_nonneg (f x))
  · rw [Set.indicator_of_notMem (show x ∉ {x : Configuration N | r ≤ ‖x‖} from hr),norm_zero]
    positivity

#print axioms exteriorL2_ae
#print axioms exponential_L2_tail_bound
end TheoremT.Continuum
