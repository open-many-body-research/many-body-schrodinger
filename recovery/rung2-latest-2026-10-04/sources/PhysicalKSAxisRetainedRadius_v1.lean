import PhysicalKSAxisPolynomialData_v1
import PhysicalKSAnalyticAxisSlice_v1

/-! Compatibility of the actual grouped coefficient rate with the actual
bounded analytic axis radius. The numerical shrinkage is proved explicitly. -/
noncomputable section
set_option autoImplicit false
namespace TheoremT.Continuum

theorem physicalKSAxisSeriesRate_pos {M A : ℝ} (hA : 1 ≤ A) :
    0 < physicalKSAxisSeriesRate M A := by
  have hS : 0 < 7*physicalKSPointwiseRate M A :=
    mul_pos (by norm_num) (physicalKSPointwiseRate_pos hA)
  unfold physicalKSAxisSeriesRate
  positivity

theorem physicalKSAxisSeriesRate_mul_analyticAxisRadius_le_half {M A : ℝ} (hA : 1 ≤ A) :
    physicalKSAxisSeriesRate M A*physicalKSAnalyticAxisRadius M A ≤ 1/2 := by
  let S := 7*physicalKSPointwiseRate M A
  let D := 32*S^2
  let r := physicalKSAnalyticAxisRadius M A
  have hS : 0 < S := mul_pos (by norm_num) (physicalKSPointwiseRate_pos hA)
  have hD : 0 < D := by dsimp [D]; positivity
  have hrD : r ≤ (4*D)⁻¹ := min_le_left _ _
  have hrS : r ≤ (4*S)⁻¹ := min_le_right _ _
  have hDr : r*(4*D) ≤ 1 := (le_div_iff₀ (by positivity : 0 < 4*D)).mp
    (by simpa only [one_div] using hrD)
  have hSr : r*(4*S) ≤ 1 := (le_div_iff₀ (by positivity : 0 < 4*S)).mp
    (by simpa only [one_div] using hrS)
  change (2*max D S)*r ≤ 1/2
  rcases le_total D S with h | h
  · rw [max_eq_right h]
    nlinarith
  · rw [max_eq_left h]
    nlinarith

theorem physicalKSAxisSeriesRate_mul_retainedRadius_le_one {M A h : ℝ}
    (hA : 1 ≤ A) (hh : h ≤ physicalKSAnalyticAxisRadius M A) :
    physicalKSAxisSeriesRate M A*h ≤ 1 := by
  have hprod := mul_le_mul_of_nonneg_left hh (physicalKSAxisSeriesRate_pos (M := M) hA).le
  have hhalf := physicalKSAxisSeriesRate_mul_analyticAxisRadius_le_half (M := M) hA
  linarith

end TheoremT.Continuum
