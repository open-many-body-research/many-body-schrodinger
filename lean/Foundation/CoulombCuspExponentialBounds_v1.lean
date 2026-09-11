import CoulombCuspRegularizationError_v1

noncomputable section
open Filter
open scoped Topology
namespace TheoremT.Continuum

theorem coulombCusp_regularization_error_le_coefficient (N : ℕ) (Z : ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (x : Configuration N) :
    |regularizedCoulombCusp N Z δ x-coulombCusp N Z x| ≤ cuspRegularizationCoefficient N Z := by
  have hs : Real.sqrt δ ≤ 1 := by nlinarith [Real.sq_sqrt hδ.le,Real.sqrt_nonneg δ]
  exact (coulombCusp_regularization_error N Z hδ x).trans
    (by simpa using mul_le_mul_of_nonneg_left hs (cuspRegularizationCoefficient_nonneg N Z))

theorem regularized_cusp_exp_neg_bound (N : ℕ) (Z : ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (x : Configuration N) :
    Real.exp (-regularizedCoulombCusp N Z δ x) ≤
      Real.exp (cuspRegularizationCoefficient N Z)*Real.exp (-coulombCusp N Z x) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := (abs_le.mp (coulombCusp_regularization_error_le_coefficient N Z hδ hδ1 x)).1
  linarith

theorem regularized_cusp_exp_neg_tendsto (N : ℕ) (Z : ℝ) (x : Configuration N) :
    Tendsto (fun n => Real.exp (-regularizedCoulombCusp N Z (radiusRegularization n) x)) atTop
      (𝓝 (Real.exp (-coulombCusp N Z x))) :=
  (Real.continuous_exp.tendsto _).comp
    ((regularizedCoulombCusp_tendsto N Z radiusRegularization_tendsto x).neg)

#print axioms regularized_cusp_exp_neg_bound
end TheoremT.Continuum
