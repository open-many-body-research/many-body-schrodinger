import BoundedExponentialWeights_v1
import PuncturedCutoffGeometry_v1

/-! Smooth saturated exponential weights vanishing on an actual exterior
coercivity ball. All L-infinity and weak-test admissibility facts are proved. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace TheoremT.Continuum

def exteriorTaper (N : ℕ) (R : ℝ) (x : Configuration N) : ℝ := 1-scaledCutoff N R x

theorem exteriorTaper_nonneg (N : ℕ) (R : ℝ) (x : Configuration N) :
    0 ≤ exteriorTaper N R x := sub_nonneg.mpr (scaledCutoff_le_one N R x)

theorem exteriorTaper_le_one (N : ℕ) (R : ℝ) (x : Configuration N) :
    exteriorTaper N R x ≤ 1 := sub_le_self _ (scaledCutoff_nonneg N R x)

theorem exteriorTaper_contDiff (N : ℕ) (R : ℝ) :
    ContDiff ℝ ∞ (exteriorTaper N R) := contDiff_const.sub (scaledCutoff_contDiff N R)

theorem exteriorTaper_memLp_top (N : ℕ) (R : ℝ) : MemLp (exteriorTaper N R) ⊤ volume := by
  apply memLp_top_of_bound (exteriorTaper_contDiff N R).continuous.aestronglyMeasurable 1
  exact Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (exteriorTaper_nonneg N R x)]
    exact exteriorTaper_le_one N R x)

def exteriorExpWeight (N : ℕ) (R a L : ℝ) (x : Configuration N) : ℝ :=
  exteriorTaper N R x * boundedExpWeight N a L x

theorem exteriorExpWeight_contDiff (N : ℕ) (R a : ℝ) {L : ℝ} (hL : 0 < L) :
    ContDiff ℝ ∞ (exteriorExpWeight N R a L) :=
  (exteriorTaper_contDiff N R).mul (boundedExpWeight_contDiff N a hL)

theorem exteriorExpWeight_memLp_top (N : ℕ) (R a : ℝ) {L : ℝ} (hL : 0 < L) :
    MemLp (exteriorExpWeight N R a L) ⊤ volume :=
  (boundedExpWeight_memLp_top N a hL).mul' (exteriorTaper_memLp_top N R)

theorem exteriorExpWeight_zero_on_ball {N : ℕ} {R : ℝ} (hR : 0 < R) (a L : ℝ)
    (x : Configuration N) (hx : ‖x‖ ≤ R) : exteriorExpWeight N R a L x = 0 := by
  simp only [exteriorExpWeight,exteriorTaper,scaledCutoff_eq_one hR hx,sub_self,zero_mul]

theorem exteriorTaper_eq_one_of_exterior {N : ℕ} {R : ℝ} (hR : 0 < R)
    (x : Configuration N) (hx : 2*R ≤ ‖x‖) : exteriorTaper N R x = 1 := by
  simp only [exteriorTaper,scaledCutoff_eq_zero_of_two_mul_le hR hx,sub_zero]

theorem exteriorExpWeight_partial {N : ℕ} (R a : ℝ) {L : ℝ} (hL : 0 < L)
    (x : Configuration N) (k : Coordinate N) :
    fderiv ℝ (exteriorExpWeight N R a L) x (coordinateVector k) =
      exteriorTaper N R x * fderiv ℝ (boundedExpWeight N a L) x (coordinateVector k) -
        fderiv ℝ (scaledCutoff N R) x (coordinateVector k) * boundedExpWeight N a L x := by
  have hc := ((scaledCutoff_contDiff N R).differentiable (by simp) x).hasFDerivAt
  have hw := ((boundedExpWeight_contDiff N a hL).differentiable (by simp) x).hasFDerivAt
  have h := ((hasFDerivAt_const (1 : ℝ) x).sub hc).mul hw
  change HasFDerivAt (exteriorExpWeight N R a L) _ x at h
  rw [h.fderiv]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply,ContinuousLinearMap.zero_apply,smul_eq_mul,
    zero_sub,neg_mul,exteriorTaper,Pi.sub_apply,ContinuousLinearMap.neg_apply]
  ring

theorem exteriorExpWeight_partial_memLp_top (N : ℕ) {R a L : ℝ}
    (hR : 0 < R) (ha : 0 ≤ a) (hL : 0 < L) (k : Coordinate N) :
    MemLp (fun x => fderiv ℝ (exteriorExpWeight N R a L) x (coordinateVector k)) ⊤ volume := by
  have h1 := (boundedExpWeight_partial_memLp_top N ha hL k).mul' (r := ⊤)
    (exteriorTaper_memLp_top N R)
  have hs : MemLp (fun x => fderiv ℝ (scaledCutoff N R) x (coordinateVector k)) ⊤ volume :=
    (((scaledCutoff_contDiff N R).continuous_fderiv (by simp)).clm_apply
      continuous_const).memLp_top_of_hasCompactSupport
        ((scaledCutoff_hasCompactSupport N hR).fderiv_apply ℝ (coordinateVector k)) volume
  have h2 := (boundedExpWeight_memLp_top N a hL).mul' (r := ⊤) hs
  apply (h1.sub h2).ae_eq
  exact Eventually.of_forall (fun x => (exteriorExpWeight_partial R a hL x k).symm)

theorem exteriorExpWeight_tendsto (N : ℕ) (R a : ℝ) (x : Configuration N) :
    Tendsto (fun n : ℕ => exteriorExpWeight N R a ((n : ℝ)+1) x) atTop
      (𝓝 (exteriorTaper N R x * Real.exp (a*smoothConfigurationRadius N x))) :=
  (boundedExpWeight_tendsto N a x).const_mul (exteriorTaper N R x)

#print axioms exteriorExpWeight_partial
#print axioms exteriorExpWeight_partial_memLp_top
#print axioms exteriorExpWeight_tendsto
end TheoremT.Continuum
