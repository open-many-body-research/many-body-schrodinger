import HardyWeakConvolution_v3
import HardyLimit_v1

/-! Transfer mechanism from compact smooth weighted estimates to actual weak
derivative data. The compact-core estimate and approximating kernels are explicit
hypotheses here, to be discharged separately for each physical multiplier. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ContDiff Topology
namespace TheoremT.Continuum

theorem mollified_gradient_energy_le {N : ℕ} {f : SpatialL2 N}
    (d : Coordinate N → SpatialL2 N) (hd : ∀ k, WeakPartial f (d k) k)
    (η : Configuration N → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hηn : ∀ x, 0 ≤ η x) (hηone : (∫ x, η x) = 1) :
    (∫ x, ∑ k : Coordinate N, ‖fderiv ℝ (mollify η f) x (coordinateVector k)‖^2) ≤
      (∫ x, ∑ k : Coordinate N, ‖d k x‖^2) := by
  have hb := fun k => mollify_derivative_memLp_two_and_bound (hd k) η hη hcη hηn hηone
  have hi := fun k => (hb k).1.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hdint := fun k => (Lp.memLp (d k)).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  rw [integral_finset_sum Finset.univ (fun k _ => hi k),
    integral_finset_sum Finset.univ (fun k _ => hdint k)]
  exact Finset.sum_le_sum (fun k _ => (hb k).2)

/-- A compact smooth core estimate passes to an actual weak-derivative input
once a compact normalized mollifier approximation with a.e. convergence is given.
This general theorem does not itself establish the physical compact-core estimate. -/
theorem compact_core_bound_passes_to_weak_limit {N : ℕ} (W : Configuration N → ℝ)
    (hW : ∀ x, 0 ≤ W x) {K : ℝ} (hK : 0 ≤ K)
    (hcore : ∀ u : Configuration N → ℂ, ContDiff ℝ ∞ u → HasCompactSupport u →
      Integrable (fun x => W x * ‖u x‖^2) volume ∧
        (∫ x, W x * ‖u x‖^2) ≤ K *
          (∫ x, ∑ k : Coordinate N, ‖fderiv ℝ u x (coordinateVector k)‖^2))
    (f : SpatialL2 N) (d : Coordinate N → SpatialL2 N)
    (hd : ∀ k, WeakPartial f (d k) k)
    (η : ℕ → Configuration N → ℝ)
    (hη : ∀ n, ContDiff ℝ ∞ (η n)) (hcη : ∀ n, HasCompactSupport (η n))
    (hηn : ∀ n x, 0 ≤ η n x) (hηone : ∀ n, (∫ x, η n x) = 1)
    (hcompact : ∀ n, HasCompactSupport (mollify (η n) f))
    (hlim : ∀ᵐ x, Tendsto (fun n => mollify (η n) f x) atTop (𝓝 (f x))) :
    Integrable (fun x => W x * ‖f x‖^2) volume ∧
      (∫ x, W x * ‖f x‖^2) ≤ K * (∫ x, ∑ k : Coordinate N, ‖d k x‖^2) := by
  have happ n := hcore (mollify (η n) f)
    (mollify_contDiff (η n) (hη n) (hcη n) f) (hcompact n)
  apply TheoremT.HardyLimit.integrable_and_integral_le_of_nonneg_limit
    (fun n => (happ n).1)
  · intro n
    exact Eventually.of_forall (fun x => mul_nonneg (hW x) (sq_nonneg _))
  · exact Eventually.of_forall (fun x => mul_nonneg (hW x) (sq_nonneg _))
  · filter_upwards [hlim] with x hx
    exact tendsto_const_nhds.mul (hx.norm.pow 2)
  · intro n
    exact (happ n).2.trans (mul_le_mul_of_nonneg_left
      (mollified_gradient_energy_le d hd (η n) (hη n) (hcη n) (hηn n) (hηone n)) hK)
  · exact mul_nonneg hK (integral_nonneg (fun x => Finset.sum_nonneg (fun k _ => sq_nonneg _)))

#print axioms mollified_gradient_energy_le
#print axioms compact_core_bound_passes_to_weak_limit
end TheoremT.Continuum
