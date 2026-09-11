import ContinuumFoundation_v1
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-! Relate the Fréchet derivative used by Mathlib's Sobolev inequality to
the actual coordinate derivatives in this project's weak Sobolev domain. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace TheoremT.Continuum

theorem configuration_clm_norm_le_sum (N : ℕ) (L : Configuration N →L[ℝ] ℂ) :
    ‖L‖ ≤ ∑ k : Coordinate N, ‖L (coordinateVector k)‖ := by
  classical
  apply ContinuousLinearMap.opNorm_le_bound L (Finset.sum_nonneg (fun k _ => norm_nonneg _))
  intro x
  have hx : x = ∑ k : Coordinate N, x k • coordinateVector k := by
    ext l
    simp [coordinateVector,Pi.single_apply]
  have hL : L x = ∑ k : Coordinate N, x k • L (coordinateVector k) := by
    simpa only [map_sum,map_smul] using congrArg L hx
  have hk (k : Coordinate N) : |x k| ≤ ‖x‖ := by
    simpa [coordinateVector,EuclideanSpace.inner_single_right] using
      abs_real_inner_le_norm x (coordinateVector k)
  rw [hL]
  apply (norm_sum_le _ _).trans
  calc
    (∑ k, ‖x k • L (coordinateVector k)‖) =
      ∑ k, |x k| * ‖L (coordinateVector k)‖ := by simp only [norm_smul,Real.norm_eq_abs]
    _ ≤ ∑ k, ‖x‖*‖L (coordinateVector k)‖ :=
      Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_right (hk k) (norm_nonneg _))
    _ = (∑ k, ‖L (coordinateVector k)‖)*‖x‖ := by rw [← Finset.mul_sum]; ring

#print axioms configuration_clm_norm_le_sum
end TheoremT.Continuum
