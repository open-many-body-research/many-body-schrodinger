import BoundedExponentialWeights_v1
import SaturatedExponentialSecond_v1
import SmoothConfigurationRadiusSecond_v1

/-! Cap-independent relative mixed second derivative bounds for the actual
smooth exponential weights, including boundedness needed for weak H² tests. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff
namespace TheoremT.Continuum

theorem boundedExpWeight_mixed_partial {N : ℕ} (a : ℝ) {L : ℝ} (hL : 0 < L)
    (x : Configuration N) (k l : Coordinate N) :
    fderiv ℝ (fun y => fderiv ℝ (boundedExpWeight N a L) y (coordinateVector k))
      x (coordinateVector l) =
      deriv (deriv (saturatedExp a L)) (smoothConfigurationRadius N x) *
        fderiv ℝ (smoothConfigurationRadius N) x (coordinateVector l) *
        fderiv ℝ (smoothConfigurationRadius N) x (coordinateVector k) +
      deriv (saturatedExp a L) (smoothConfigurationRadius N x) *
        fderiv ℝ (fun y => fderiv ℝ (smoothConfigurationRadius N) y (coordinateVector k))
          x (coordinateVector l) := by
  have hfun : (fun y => fderiv ℝ (boundedExpWeight N a L) y (coordinateVector k)) =
      fun y => deriv (saturatedExp a L) (smoothConfigurationRadius N y) *
        fderiv ℝ (smoothConfigurationRadius N) y (coordinateVector k) :=
    funext (fun y => boundedExpWeight_partial a hL y k)
  rw [hfun]
  have hr := ((smoothConfigurationRadius_contDiff N).differentiable (by simp) x).hasFDerivAt
  have hs := ((saturatedExp_deriv_hasDerivAt a hL (smoothConfigurationRadius N x)).differentiableAt.hasDerivAt).comp_hasFDerivAt x hr
  have hd : ContDiff ℝ ∞ (fun y : Configuration N =>
      fderiv ℝ (smoothConfigurationRadius N) y (coordinateVector k)) :=
    ((smoothConfigurationRadius_contDiff N).fderiv_right
      (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  have h := hs.mul ((hd.differentiable (by simp) x).hasFDerivAt)
  change HasFDerivAt (fun y => deriv (saturatedExp a L) (smoothConfigurationRadius N y) *
    fderiv ℝ (smoothConfigurationRadius N) y (coordinateVector k)) _ x at h
  rw [h.fderiv]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
  simp only [Function.comp_apply]
  ring

theorem boundedExpWeight_mixed_partial_abs_le {N : ℕ} {a L : ℝ}
    (ha : 0 ≤ a) (hL : 0 < L) (x : Configuration N) (k l : Coordinate N) :
    |fderiv ℝ (fun y => fderiv ℝ (boundedExpWeight N a L) y (coordinateVector k))
      x (coordinateVector l)| ≤ (a^2+2*a)*boundedExpWeight N a L x := by
  rw [boundedExpWeight_mixed_partial a hL]
  have hs := saturatedExp_second_deriv_abs_le a hL (smoothConfigurationRadius N x)
  have hd := saturatedExp_deriv_bounds ha hL (smoothConfigurationRadius N x)
  have hk := smoothConfigurationRadius_partial_abs_le_one x k
  have hl := smoothConfigurationRadius_partial_abs_le_one x l
  have hkl := smoothConfigurationRadius_mixed_partial_abs_le_two x k l
  have hwpos := saturatedExp_pos a hL (smoothConfigurationRadius N x)
  have h1 := mul_le_mul (mul_le_mul hs hl (abs_nonneg _) (by positivity)) hk
    (abs_nonneg _) (by positivity)
  have h2 := mul_le_mul hd.2 hkl (abs_nonneg _) (by positivity)
  have ht := abs_add_le
    (deriv (deriv (saturatedExp a L)) (smoothConfigurationRadius N x) *
      fderiv ℝ (smoothConfigurationRadius N) x (coordinateVector l) *
      fderiv ℝ (smoothConfigurationRadius N) x (coordinateVector k))
    (deriv (saturatedExp a L) (smoothConfigurationRadius N x) *
      fderiv ℝ (fun y => fderiv ℝ (smoothConfigurationRadius N) y (coordinateVector k))
        x (coordinateVector l))
  simp only [abs_mul,abs_of_nonneg hd.1] at ht
  change _ ≤ (a^2+2*a)*saturatedExp a L (smoothConfigurationRadius N x)
  nlinarith

theorem boundedExpWeight_mixed_partial_memLp_top (N : ℕ) {a L : ℝ}
    (ha : 0 ≤ a) (hL : 0 < L) (k l : Coordinate N) :
    MemLp (fun x => fderiv ℝ (fun y => fderiv ℝ (boundedExpWeight N a L) y (coordinateVector k))
      x (coordinateVector l)) ⊤ volume := by
  have hd : ContDiff ℝ ∞ (fun y : Configuration N =>
      fderiv ℝ (boundedExpWeight N a L) y (coordinateVector k)) :=
    ((boundedExpWeight_contDiff N a hL).fderiv_right
      (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  apply memLp_top_of_bound ((hd.continuous_fderiv (by simp)).clm_apply
    continuous_const).aestronglyMeasurable ((a^2+2*a)*L)
  exact Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs]
    exact (boundedExpWeight_mixed_partial_abs_le ha hL x k l).trans
      (mul_le_mul_of_nonneg_left (boundedExpWeight_le_cap N a hL x) (by positivity)))

#print axioms boundedExpWeight_mixed_partial
#print axioms boundedExpWeight_mixed_partial_abs_le
#print axioms boundedExpWeight_mixed_partial_memLp_top
end TheoremT.Continuum
