import SmoothLocalTestProduct_v1
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [IsLocallyFiniteMeasure μ]

theorem local_smooth_test_smul_integrable {φ : E → ℝ} {u : E → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hu : ∀ x ∈ tsupport φ, ContDiffAt ℝ ∞ u x) :
    Integrable (fun x => φ x • u x) μ :=
  (smooth_smul_of_smooth_on_tsupport hφ hu).continuous.integrable_of_hasCompactSupport hc.smul_right

theorem local_second_directional_integration_by_parts [μ.IsAddHaarMeasure]
    {φ : E → ℝ} {u : E → ℂ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hu : ∀ x ∈ tsupport φ, ContDiffAt ℝ ∞ u x) (v : E) :
    (∫ x, fderiv ℝ (fun y => fderiv ℝ φ y v) x v • u x ∂μ) =
      ∫ x, φ x • fderiv ℝ (fun y => fderiv ℝ u y v) x v ∂μ := by
  let Dφ : E → ℝ := fun x => fderiv ℝ φ x v
  let Du : E → ℂ := fun x => fderiv ℝ u x v
  have hDφ : ContDiff ℝ ∞ Dφ :=
    (hφ.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  have hcDφ : HasCompactSupport Dφ := hc.fderiv_apply ℝ v
  have hsDφ : tsupport Dφ ⊆ tsupport φ := tsupport_fderiv_apply_subset ℝ v
  have hDu (x : E) (hx : x ∈ tsupport φ) : ContDiffAt ℝ ∞ Du x :=
    local_contDiffAt_directional_derivative (hu x hx) v
  have hDDu (x : E) (hx : x ∈ tsupport φ) :
      ContDiffAt ℝ ∞ (fun y => fderiv ℝ Du y v) x :=
    local_contDiffAt_directional_derivative (hDu x hx) v
  have h1 := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (μ := μ) (f := φ) (g := Du) (v := v)
    (local_smooth_test_smul_integrable hDφ hcDφ (fun x hx => hDu x (hsDφ hx)))
    (local_smooth_test_smul_integrable hφ hc hDDu)
    (local_smooth_test_smul_integrable hφ hc hDu)
    (fun x _ => hφ.differentiable (by simp) x)
    (fun x hx => (hDu x hx).differentiableAt (by simp))
  have hDDφ : ContDiff ℝ ∞ (fun x => fderiv ℝ Dφ x v) :=
    (hDφ.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  have hsDDφ : tsupport (fun x => fderiv ℝ Dφ x v) ⊆ tsupport φ :=
    (tsupport_fderiv_apply_subset ℝ v).trans hsDφ
  have h2 := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (μ := μ) (f := Dφ) (g := u) (v := v)
    (local_smooth_test_smul_integrable hDDφ (hcDφ.fderiv_apply ℝ v) (fun x hx => hu x (hsDDφ hx)))
    (local_smooth_test_smul_integrable hDφ hcDφ (fun x hx => hDu x (hsDφ hx)))
    (local_smooth_test_smul_integrable hDφ hcDφ (fun x hx => hu x (hsDφ hx)))
    (fun x _ => hDφ.differentiable (by simp) x)
    (fun x hx => (hu x (hsDφ hx)).differentiableAt (by simp))
  rw [h2,neg_neg] at h1
  exact h1.symm

#print axioms local_second_directional_integration_by_parts
end TheoremT.Continuum
