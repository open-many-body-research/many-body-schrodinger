import ContinuumFoundation_v1
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! A globally smooth radius sqrt(1+|x|²) on actual configuration space.
It dominates the physical Euclidean radius and has gradient norm at most one. -/
noncomputable section
open scoped ContDiff BigOperators
namespace TheoremT.Continuum

def smoothConfigurationRadius (N : ℕ) (x : Configuration N) : ℝ :=
  Real.sqrt (1+‖x‖^2)

theorem smoothConfigurationRadius_pos {N : ℕ} (x : Configuration N) :
    0 < smoothConfigurationRadius N x := Real.sqrt_pos.mpr (by positivity)

theorem smoothConfigurationRadius_sq {N : ℕ} (x : Configuration N) :
    (smoothConfigurationRadius N x)^2 = 1+‖x‖^2 := Real.sq_sqrt (by positivity)

theorem norm_le_smoothConfigurationRadius {N : ℕ} (x : Configuration N) :
    ‖x‖ ≤ smoothConfigurationRadius N x := by
  have h := smoothConfigurationRadius_sq x
  nlinarith [smoothConfigurationRadius_pos x,norm_nonneg x]

theorem smoothConfigurationRadius_le_norm_add_one {N : ℕ} (x : Configuration N) :
    smoothConfigurationRadius N x ≤ ‖x‖+1 := by
  have h := smoothConfigurationRadius_sq x
  nlinarith [smoothConfigurationRadius_pos x,norm_nonneg x]

theorem smoothConfigurationRadius_contDiff (N : ℕ) :
    ContDiff ℝ ∞ (smoothConfigurationRadius N) :=
  (contDiff_const.add (contDiff_norm_sq ℝ)).sqrt (fun x => by positivity)

theorem smoothConfigurationRadius_partial {N : ℕ} (x : Configuration N) (k : Coordinate N) :
    fderiv ℝ (smoothConfigurationRadius N) x (coordinateVector k) =
      x k / smoothConfigurationRadius N x := by
  have hh := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_add 1).sqrt
    (by positivity : 1+‖x‖^2 ≠ 0)
  change HasFDerivAt (smoothConfigurationRadius N) _ x at hh
  rw [hh.fderiv]
  have hi : inner ℝ x (coordinateVector k) = x k := by
    simp [coordinateVector,EuclideanSpace.inner_single_right]
  simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.add_apply,
    innerSL_apply_apply,smul_eq_mul,two_smul]
  rw [hi]
  unfold smoothConfigurationRadius
  ring

theorem smoothConfigurationRadius_gradient_sq {N : ℕ} (x : Configuration N) :
    (∑ k : Coordinate N, (fderiv ℝ (smoothConfigurationRadius N) x (coordinateVector k))^2) =
      ‖x‖^2 / (smoothConfigurationRadius N x)^2 := by
  simp only [smoothConfigurationRadius_partial,div_pow,← Finset.sum_div]
  rw [EuclideanSpace.real_norm_sq_eq]

theorem smoothConfigurationRadius_gradient_sq_le_one {N : ℕ} (x : Configuration N) :
    (∑ k : Coordinate N, (fderiv ℝ (smoothConfigurationRadius N) x (coordinateVector k))^2) ≤ 1 := by
  rw [smoothConfigurationRadius_gradient_sq,smoothConfigurationRadius_sq]
  exact (div_le_one (by positivity)).mpr (by linarith)

theorem smoothConfigurationRadius_partial_abs_le_one {N : ℕ}
    (x : Configuration N) (k : Coordinate N) :
    |fderiv ℝ (smoothConfigurationRadius N) x (coordinateVector k)| ≤ 1 := by
  have hs := Finset.single_le_sum (fun i _ => sq_nonneg
    (fderiv ℝ (smoothConfigurationRadius N) x (coordinateVector i))) (Finset.mem_univ k)
  have h := smoothConfigurationRadius_gradient_sq_le_one x
  rw [abs_le]
  constructor <;> nlinarith

#print axioms smoothConfigurationRadius_partial
#print axioms smoothConfigurationRadius_gradient_sq_le_one
end TheoremT.Continuum
