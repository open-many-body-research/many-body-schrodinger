import RegularizedCoulombCuspDerivatives_v1
import CoulombFiniteCombinationBound_v1

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace TheoremT.Continuum

def cuspDirectionalBound (N : ℕ) (Z : ℝ) (v : Configuration N) : ℝ :=
  |Z| * (∑ i : Fin N, ‖electronPositionCLM i v‖)+
    (1/2:ℝ)*(∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j : Fin N => i<j),
      ‖pairDifferenceCLM i j v‖)

def cuspHessianBound (N : ℕ) (Z : ℝ) (v w x : Configuration N) : ℝ :=
  |Z| * (∑ i : Fin N, 2*‖electronPositionCLM i v‖*‖electronPositionCLM i w‖/‖position x i‖)+
    (1/2:ℝ)*(∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j : Fin N => i<j),
      2*‖pairDifferenceCLM i j v‖*‖pairDifferenceCLM i j w‖/‖position x i-position x j‖)

theorem cuspDirectionalBound_nonneg (N : ℕ) (Z : ℝ) (v : Configuration N) :
    0 ≤ cuspDirectionalBound N Z v := by unfold cuspDirectionalBound; positivity

theorem cuspHessianBound_nonneg (N : ℕ) (Z : ℝ) (v w x : Configuration N) :
    0 ≤ cuspHessianBound N Z v w x := by unfold cuspHessianBound; positivity

theorem regularizedCoulombCusp_partial_abs_bound (N : ℕ) (Z : ℝ)
    {δ : ℝ} (hδ : 0 < δ) (x v : Configuration N) :
    |fderiv ℝ (regularizedCoulombCusp N Z δ) x v| ≤ cuspDirectionalBound N Z v := by
  rw [regularizedCoulombCusp_partial_sum _ _ hδ]
  exact coulomb_finite_combination_abs_bound N Z _ _ _ _
    (fun i => regularizedLinearRadius_partial_abs_bound _ hδ x v)
    (fun i j _ => regularizedLinearRadius_partial_abs_bound _ hδ x v)

theorem regularizedCoulombCusp_mixed_coulomb_bound (N : ℕ) (Z : ℝ)
    {δ : ℝ} (hδ : 0 < δ) {x : Configuration N} (hx : collisionFree x) (v w : Configuration N) :
    |fderiv ℝ (fun y => fderiv ℝ (regularizedCoulombCusp N Z δ) y v) x w| ≤
      cuspHessianBound N Z v w x := by
  rw [regularizedCoulombCusp_mixed_sum _ _ hδ]
  exact coulomb_finite_combination_abs_bound N Z _ _ _ _
    (fun i => regularizedLinearRadius_mixed_coulomb_bound _ hδ (hx.1 i) v w)
    (fun i j hij => regularizedLinearRadius_mixed_coulomb_bound _ hδ
      (sub_ne_zero.mpr (hx.2 i j (ne_of_lt hij))) v w)

#print axioms regularizedCoulombCusp_partial_abs_bound
#print axioms regularizedCoulombCusp_mixed_coulomb_bound
end TheoremT.Continuum
