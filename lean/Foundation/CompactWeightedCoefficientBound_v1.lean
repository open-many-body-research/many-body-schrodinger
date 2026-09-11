import SmoothLocalizedExponential_v1
import CoulombCuspExponentialBounds_v1

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum

theorem compact_cusp_weighted_coefficient_bound (N : ℕ) (Z : ℝ)
    {χ : Configuration N → ℝ} (hχ : Continuous χ) (hc : HasCompactSupport χ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Configuration N,
      Real.exp (cuspRegularizationCoefficient N Z)*Real.exp (-coulombCusp N Z x)*|χ x| ≤ C := by
  have he : Continuous (fun x : Configuration N =>
      Real.exp (cuspRegularizationCoefficient N Z)*Real.exp (-coulombCusp N Z x)*|χ x|) :=
    (continuous_const.mul (Real.continuous_exp.comp (coulombCusp_continuous N Z).neg)).mul hχ.abs
  have hce : HasCompactSupport (fun x : Configuration N =>
      Real.exp (cuspRegularizationCoefficient N Z)*Real.exp (-coulombCusp N Z x)*|χ x|) :=
    hc.abs.mul_left
  obtain ⟨C,hC⟩ := hce.exists_bound_of_continuous he
  refine ⟨C,(norm_nonneg _).trans (hC 0),?_⟩
  intro x
  simpa only [Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤
    Real.exp (cuspRegularizationCoefficient N Z)*Real.exp (-coulombCusp N Z x)*|χ x|)] using hC x

theorem localized_cusp_regularization_bound (N : ℕ) (Z : ℝ)
    {χ : Configuration N → ℝ} (hχ : Continuous χ) (hc : HasCompactSupport χ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ x : Configuration N,
      |χ x*Real.exp (-regularizedCoulombCusp N Z δ x)| ≤ C := by
  obtain ⟨C,hC0,hC⟩ := compact_cusp_weighted_coefficient_bound N Z hχ hc
  refine ⟨C,hC0,?_⟩
  intro δ hδ hδ1 x
  rw [abs_mul,abs_of_pos (Real.exp_pos _)]
  have he := mul_le_mul_of_nonneg_left (regularized_cusp_exp_neg_bound N Z hδ hδ1 x) (abs_nonneg (χ x))
  exact he.trans (by simpa only [mul_comm,mul_left_comm,mul_assoc] using hC x)

#print axioms localized_cusp_regularization_bound
end TheoremT.Continuum
