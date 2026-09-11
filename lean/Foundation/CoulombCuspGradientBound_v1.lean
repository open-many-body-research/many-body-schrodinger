import CoulombCuspDerivativeLimits_v1
import CoulombCuspDerivativeBounds_v1

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace TheoremT.Continuum

theorem coulombCuspGradient_abs_bound (N : ℕ) (Z : ℝ) (v x : Configuration N) :
    |coulombCuspGradient N Z v x| ≤ cuspDirectionalBound N Z v := by
  exact coulomb_finite_combination_abs_bound N Z _ _ _ _
    (fun i => linearRadiusGradient_abs_bound _ v x)
    (fun i j _ => linearRadiusGradient_abs_bound _ v x)

def cuspCoordinateGradientSquareBound (N : ℕ) (Z : ℝ) : ℝ :=
  ∑ k : Coordinate N, (cuspDirectionalBound N Z (coordinateVector k))^2

theorem cuspCoordinateGradientSquareBound_nonneg (N : ℕ) (Z : ℝ) :
    0 ≤ cuspCoordinateGradientSquareBound N Z := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem coulombCuspGradient_sq_sum_bound (N : ℕ) (Z : ℝ) (x : Configuration N) :
    (∑ k : Coordinate N, (coulombCuspGradient N Z (coordinateVector k) x)^2) ≤
      cuspCoordinateGradientSquareBound N Z := by
  apply Finset.sum_le_sum
  intro k hk
  have h := coulombCuspGradient_abs_bound N Z (coordinateVector k) x
  have hc := cuspDirectionalBound_nonneg N Z (coordinateVector k)
  nlinarith [sq_abs (coulombCuspGradient N Z (coordinateVector k) x),
    abs_nonneg (coulombCuspGradient N Z (coordinateVector k) x)]

theorem coulombCusp_zero_order_coefficient_bound (N : ℕ) (Z E : ℝ) (x : Configuration N) :
    |(∑ k : Coordinate N, (coulombCuspGradient N Z (coordinateVector k) x)^2)+2*E| ≤
      cuspCoordinateGradientSquareBound N Z+2*|E| := by
  have hs : 0 ≤ ∑ k : Coordinate N, (coulombCuspGradient N Z (coordinateVector k) x)^2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  calc
    _ ≤ |∑ k : Coordinate N, (coulombCuspGradient N Z (coordinateVector k) x)^2|+|2*E| := abs_add_le _ _
    _ = (∑ k : Coordinate N, (coulombCuspGradient N Z (coordinateVector k) x)^2)+2*|E| := by
      rw [abs_of_nonneg hs,abs_mul]; norm_num
    _ ≤ _ := add_le_add (coulombCuspGradient_sq_sum_bound N Z x) le_rfl

#print axioms coulombCuspGradient_abs_bound
#print axioms coulombCusp_zero_order_coefficient_bound
end TheoremT.Continuum
