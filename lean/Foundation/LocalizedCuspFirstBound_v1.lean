import CompactWeightedCoefficientBound_v1
import CoulombCuspDerivativeBounds_v1

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum

theorem localized_cusp_partial_uniform_bound (N : ℕ) (Z : ℝ)
    {χ : Configuration N → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (v : Configuration N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ x : Configuration N,
      |fderiv ℝ (fun y => χ y*Real.exp (-regularizedCoulombCusp N Z δ y)) x v| ≤ C := by
  obtain ⟨A,hA0,hA⟩ := localized_cusp_regularization_bound N Z hχ.continuous hc
  have hdχ : Continuous (fun x => fderiv ℝ χ x v) :=
    (hχ.continuous_fderiv (by simp)).clm_apply continuous_const
  obtain ⟨B,hB0,hB⟩ := localized_cusp_regularization_bound N Z hdχ (hc.fderiv_apply ℝ v)
  have hV := cuspDirectionalBound_nonneg N Z v
  refine ⟨B+A*cuspDirectionalBound N Z v,by positivity,?_⟩
  intro δ hδ hδ1 x
  rw [smooth_localized_exp_partial hχ (regularizedCoulombCusp_contDiff N Z hδ)]
  have he : Real.exp (-regularizedCoulombCusp N Z δ x)*(fderiv ℝ χ x v-
      χ x*fderiv ℝ (regularizedCoulombCusp N Z δ) x v) =
      fderiv ℝ χ x v*Real.exp (-regularizedCoulombCusp N Z δ x)-
        (χ x*Real.exp (-regularizedCoulombCusp N Z δ x))*fderiv ℝ (regularizedCoulombCusp N Z δ) x v := by ring
  rw [he]
  apply (abs_sub _ _).trans
  rw [abs_mul (χ x*Real.exp (-regularizedCoulombCusp N Z δ x))]
  exact add_le_add (hB δ hδ hδ1 x)
    (mul_le_mul (hA δ hδ hδ1 x) (regularizedCoulombCusp_partial_abs_bound N Z hδ x v)
      (abs_nonneg _) hA0)

#print axioms localized_cusp_partial_uniform_bound
end TheoremT.Continuum
