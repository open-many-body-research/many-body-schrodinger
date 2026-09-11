import LocalSecondDerivativeIBP_v1

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [IsLocallyFiniteMeasure μ]

theorem local_second_test_smul_integrable {φ : E → ℝ} {u : E → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hu : ∀ x ∈ tsupport φ, ContDiffAt ℝ ∞ u x) (v : E) :
    Integrable (fun x => fderiv ℝ (fun y => fderiv ℝ φ y v) x v • u x) μ := by
  have hd : ContDiff ℝ ∞ (fun x => fderiv ℝ φ x v) :=
    (hφ.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  apply local_smooth_test_smul_integrable
    ((hd.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const)
    ((hc.fderiv_apply ℝ v).fderiv_apply ℝ v)
  intro x hx
  exact hu x ((tsupport_fderiv_apply_subset ℝ v) ((tsupport_fderiv_apply_subset ℝ v) hx))

theorem local_test_second_smul_integrable {φ : E → ℝ} {u : E → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hu : ∀ x ∈ tsupport φ, ContDiffAt ℝ ∞ u x) (v : E) :
    Integrable (fun x => φ x • fderiv ℝ (fun y => fderiv ℝ u y v) x v) μ := by
  apply local_smooth_test_smul_integrable hφ hc
  intro x hx
  exact local_contDiffAt_directional_derivative (local_contDiffAt_directional_derivative (hu x hx) v) v

#print axioms local_second_test_smul_integrable
#print axioms local_test_second_smul_integrable
end TheoremT.Continuum
