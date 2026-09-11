import HardyLimitL2_v1
import HardyRegularized_v3

/-! Genuine three-dimensional Hardy inequality for real C¹ compactly supported
functions, composed from the proved regularized vector-field identity and Fatou.
This statement does not yet extend to arbitrary functions in the weak H¹ domain. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace TheoremT.Hardy

/-- The weighted square is integrable, and the classical Hardy constant 4
holds for real C¹ compactly supported functions on Euclidean R³. -/
theorem hardy_integrable_sq_and_bound {u : R3 → ℝ}
    (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u) :
    Integrable (fun x => (u x)^2 / ‖x‖^2) volume ∧
      (∫ x, (u x)^2 / ‖x‖^2) ≤
        4 * (∫ x, ∑ i : Fin 3, (fderiv ℝ u x (basisVector i))^2) :=
  TheoremT.HardyLimit.singularWeight_of_regularized_bounds hu.continuous huc
    (fun _ hδ => regularized_hardy_integral hδ hu huc)

/-- The singular multiplier belongs to actual Lebesgue L², together with the
Hardy energy bound. Division at the null singleton is Lean's totalized division. -/
theorem hardy_memLp_two_and_bound {u : R3 → ℝ}
    (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u) :
    MemLp (fun x => u x / ‖x‖) 2 volume ∧
      (∫ x, (u x / ‖x‖)^2) ≤
        4 * (∫ x, ∑ i : Fin 3, (fderiv ℝ u x (basisVector i))^2) :=
  TheoremT.HardyLimit.inverseNorm_memLp_of_regularized_bounds hu.continuous huc
    (fun _ hδ => regularized_hardy_integral hδ hu huc)

#print hardy_integrable_sq_and_bound
#print axioms hardy_integrable_sq_and_bound
#print hardy_memLp_two_and_bound
#print axioms hardy_memLp_two_and_bound
end TheoremT.Hardy
