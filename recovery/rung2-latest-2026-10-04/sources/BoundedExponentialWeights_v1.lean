import SmoothConfigurationRadius_v1
import SaturatedExponential_v1
import BoundedSmoothMultiplier_v1

/-! Literal smooth saturated exponentials on configuration space. Gradient
control is dimension independent; no estimate of the unknown eigenfunction
is assumed in the weight construction. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace TheoremT.Continuum

def boundedExpWeight (N : ℕ) (a L : ℝ) (x : Configuration N) : ℝ :=
  saturatedExp a L (smoothConfigurationRadius N x)

theorem boundedExpWeight_pos (N : ℕ) (a : ℝ) {L : ℝ} (hL : 0 < L)
    (x : Configuration N) : 0 < boundedExpWeight N a L x := saturatedExp_pos a hL _

theorem boundedExpWeight_le_cap (N : ℕ) (a : ℝ) {L : ℝ} (hL : 0 < L)
    (x : Configuration N) : boundedExpWeight N a L x ≤ L := saturatedExp_le_cap a hL _

theorem boundedExpWeight_le_exp (N : ℕ) (a : ℝ) {L : ℝ} (hL : 0 < L)
    (x : Configuration N) :
    boundedExpWeight N a L x ≤ Real.exp (a*smoothConfigurationRadius N x) :=
  saturatedExp_le_exp a hL _

theorem boundedExpWeight_contDiff (N : ℕ) (a : ℝ) {L : ℝ} (hL : 0 < L) :
    ContDiff ℝ ∞ (boundedExpWeight N a L) :=
  (saturatedExp_contDiff a hL).comp (smoothConfigurationRadius_contDiff N)

theorem boundedExpWeight_partial {N : ℕ} (a : ℝ) {L : ℝ} (hL : 0 < L)
    (x : Configuration N) (k : Coordinate N) :
    fderiv ℝ (boundedExpWeight N a L) x (coordinateVector k) =
      deriv (saturatedExp a L) (smoothConfigurationRadius N x) *
        fderiv ℝ (smoothConfigurationRadius N) x (coordinateVector k) := by
  have hs := ((saturatedExp_contDiff a hL).differentiable (by simp)
    (smoothConfigurationRadius N x)).hasDerivAt
  have h := hs.comp_hasFDerivAt x
    (((smoothConfigurationRadius_contDiff N).differentiable (by simp) x).hasFDerivAt)
  change HasFDerivAt (boundedExpWeight N a L) _ x at h
  rw [h.fderiv]
  rfl

theorem boundedExpWeight_partial_abs_le {N : ℕ} {a L : ℝ} (ha : 0 ≤ a) (hL : 0 < L)
    (x : Configuration N) (k : Coordinate N) :
    |fderiv ℝ (boundedExpWeight N a L) x (coordinateVector k)| ≤ a*boundedExpWeight N a L x := by
  rw [boundedExpWeight_partial a hL,abs_mul]
  have hd := saturatedExp_deriv_bounds ha hL (smoothConfigurationRadius N x)
  rw [abs_of_nonneg hd.1]
  calc
    _ ≤ deriv (saturatedExp a L) (smoothConfigurationRadius N x) * 1 :=
      mul_le_mul_of_nonneg_left (smoothConfigurationRadius_partial_abs_le_one x k) hd.1
    _ ≤ _ := by simpa only [mul_one,boundedExpWeight] using hd.2

theorem boundedExpWeight_gradient_sq_le {N : ℕ} {a L : ℝ} (ha : 0 ≤ a) (hL : 0 < L)
    (x : Configuration N) :
    (∑ k : Coordinate N, (fderiv ℝ (boundedExpWeight N a L) x (coordinateVector k))^2) ≤
      a^2 * (boundedExpWeight N a L x)^2 := by
  simp_rw [boundedExpWeight_partial a hL,mul_pow]
  rw [← Finset.mul_sum]
  have hd := saturatedExp_deriv_bounds ha hL (smoothConfigurationRadius N x)
  have hs := pow_le_pow_left₀ hd.1 hd.2 2
  calc
    _ ≤ (deriv (saturatedExp a L) (smoothConfigurationRadius N x))^2 := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (smoothConfigurationRadius_gradient_sq_le_one x) (sq_nonneg _)
    _ ≤ _ := by simpa only [mul_pow,boundedExpWeight] using hs

theorem boundedExpWeight_memLp_top (N : ℕ) (a : ℝ) {L : ℝ} (hL : 0 < L) :
    MemLp (boundedExpWeight N a L) ⊤ volume := by
  apply memLp_top_of_bound (boundedExpWeight_contDiff N a hL).continuous.aestronglyMeasurable L
  exact Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs,abs_of_pos (boundedExpWeight_pos N a hL x)]
    exact boundedExpWeight_le_cap N a hL x)

theorem boundedExpWeight_partial_memLp_top (N : ℕ) {a L : ℝ} (ha : 0 ≤ a) (hL : 0 < L)
    (k : Coordinate N) :
    MemLp (fun x => fderiv ℝ (boundedExpWeight N a L) x (coordinateVector k)) ⊤ volume := by
  apply memLp_top_of_bound
    (((boundedExpWeight_contDiff N a hL).continuous_fderiv (by simp)).clm_apply
      continuous_const).aestronglyMeasurable (a*L)
  apply Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs]
  exact (boundedExpWeight_partial_abs_le ha hL x k).trans
    (mul_le_mul_of_nonneg_left (boundedExpWeight_le_cap N a hL x) ha)

theorem boundedExpWeight_tendsto (N : ℕ) (a : ℝ) (x : Configuration N) :
    Tendsto (fun n : ℕ => boundedExpWeight N a ((n : ℝ)+1) x) atTop
      (𝓝 (Real.exp (a*smoothConfigurationRadius N x))) := saturatedExp_tendsto a _

#print axioms boundedExpWeight_gradient_sq_le
#print axioms boundedExpWeight_partial_memLp_top
#print axioms boundedExpWeight_tendsto
end TheoremT.Continuum
