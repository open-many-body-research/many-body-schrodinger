import LocalizedCuspFirstBound_v1
import RealFiveTermBound_v1

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum

theorem localized_cusp_mixed_uniform_coulomb_bound (N : ℕ) (Z : ℝ)
    {χ : Configuration N → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (v w : Configuration N) :
    ∃ M C : ℝ, 0 ≤ M ∧ 0 ≤ C ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ x : Configuration N, collisionFree x →
        |fderiv ℝ (fun y => fderiv ℝ
          (fun z => χ z*Real.exp (-regularizedCoulombCusp N Z δ z)) y v) x w| ≤
            M+C*cuspHessianBound N Z v w x := by
  obtain ⟨A,hA0,hA⟩ := localized_cusp_regularization_bound N Z hχ.continuous hc
  have hdv : ContDiff ℝ ∞ (fun x => fderiv ℝ χ x v) :=
    (hχ.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  have hdw : Continuous (fun x => fderiv ℝ χ x w) :=
    (hχ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdvw : Continuous (fun x => fderiv ℝ (fun y => fderiv ℝ χ y v) x w) :=
    (hdv.continuous_fderiv (by simp)).clm_apply continuous_const
  obtain ⟨B,hB0,hB⟩ := localized_cusp_regularization_bound N Z hdv.continuous (hc.fderiv_apply ℝ v)
  obtain ⟨C,hC0,hC⟩ := localized_cusp_regularization_bound N Z hdw (hc.fderiv_apply ℝ w)
  obtain ⟨D,hD0,hD⟩ := localized_cusp_regularization_bound N Z hdvw ((hc.fderiv_apply ℝ v).fderiv_apply ℝ w)
  have hV := cuspDirectionalBound_nonneg N Z v
  have hW := cuspDirectionalBound_nonneg N Z w
  refine ⟨D+B*cuspDirectionalBound N Z w+C*cuspDirectionalBound N Z v+
    A*cuspDirectionalBound N Z v*cuspDirectionalBound N Z w,A,by positivity,hA0,?_⟩
  intro δ hδ hδ1 x hx
  rw [smooth_localized_exp_mixed hχ (regularizedCoulombCusp_contDiff N Z hδ)]
  exact exp_weighted_five_term_bound
    (-regularizedCoulombCusp N Z δ x)
    (fderiv ℝ (fun y => fderiv ℝ χ y v) x w) (fderiv ℝ χ x v) (fderiv ℝ χ x w)
    (χ x) (χ x) (fderiv ℝ (regularizedCoulombCusp N Z δ) x v)
    (fderiv ℝ (regularizedCoulombCusp N Z δ) x w)
    (fderiv ℝ (fun y => fderiv ℝ (regularizedCoulombCusp N Z δ) y v) x w)
    D B C A (cuspDirectionalBound N Z v) (cuspDirectionalBound N Z w) (cuspHessianBound N Z v w x)
    (hD δ hδ hδ1 x) (hB δ hδ hδ1 x) (hC δ hδ hδ1 x) (hA δ hδ hδ1 x)
    (regularizedCoulombCusp_partial_abs_bound N Z hδ x v)
    (regularizedCoulombCusp_partial_abs_bound N Z hδ x w)
    (regularizedCoulombCusp_mixed_coulomb_bound N Z hδ hx v w) rfl

#print axioms localized_cusp_mixed_uniform_coulomb_bound
end TheoremT.Continuum
