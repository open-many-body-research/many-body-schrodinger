import WeakDomainAlgebra_v2

/-! Extension of the unchanged real-test WeakPartial predicate to complex
compact smooth tests. No extension to noncompact tests is assumed. -/

noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory
open scoped ContDiff

namespace TheoremT.Continuum

theorem integral_complex_test_split {N : ℕ} (f : SpatialL2 N)
    {φ : Configuration N → ℂ} (hφ : Continuous φ) (hcφ : HasCompactSupport φ) :
    (∫ x, φ x • f x) = (∫ x, (φ x).re • f x) +
      Complex.I • (∫ x, (φ x).im • f x) := by
  have hr := test_integrable f (Complex.continuous_re.comp hφ) (hcφ.comp_left rfl)
  have hi := test_integrable f (Complex.continuous_im.comp hφ) (hcφ.comp_left rfl)
  calc
    (∫ x, φ x • f x) = ∫ x, (φ x).re • f x + Complex.I • ((φ x).im • f x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      calc
        φ x • f x = ((φ x).re + (φ x).im * Complex.I : ℂ) • f x := by
          rw [Complex.re_add_im]
        _ = _ := by
          simp only [add_smul, mul_smul, Complex.coe_smul]
          rw [smul_comm ((φ x).im) Complex.I]
    _ = _ := by
      have hs := integral_add hr (Integrable.smul Complex.I hi)
      simp only [Pi.smul_apply, Function.comp_apply] at hs
      rw [hs, integral_smul]

theorem WeakPartial.complex_test {N : ℕ} {f g : SpatialL2 N} {k : Coordinate N}
    (h : WeakPartial f g k) (φ : Configuration N → ℂ)
    (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) :
    (∫ x, φ x • g x) = -(∫ x, fderiv ℝ φ x (coordinateVector k) • f x) := by
  have hre (x : Configuration N) :
      fderiv ℝ (fun y => (φ y).re) x (coordinateVector k) =
        (fderiv ℝ φ x (coordinateVector k)).re := by
    change fderiv ℝ (Complex.reCLM ∘ φ) x (coordinateVector k) = _
    rw [fderiv_comp x Complex.reCLM.differentiableAt (hφ.differentiable (by simp) x)]
    simp
  have him (x : Configuration N) :
      fderiv ℝ (fun y => (φ y).im) x (coordinateVector k) =
        (fderiv ℝ φ x (coordinateVector k)).im := by
    change fderiv ℝ (Complex.imCLM ∘ φ) x (coordinateVector k) = _
    rw [fderiv_comp x Complex.imCLM.differentiableAt (hφ.differentiable (by simp) x)]
    simp
  have hr := h (fun x => (φ x).re) (Complex.reCLM.contDiff.comp hφ) (hcφ.comp_left rfl)
  have hi := h (fun x => (φ x).im) (Complex.imCLM.contDiff.comp hφ) (hcφ.comp_left rfl)
  have hd : Continuous (fun x => fderiv ℝ φ x (coordinateVector k)) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  rw [integral_complex_test_split g hφ.continuous hcφ,
    integral_complex_test_split f hd (hcφ.fderiv_apply ℝ (coordinateVector k))]
  simp_rw [← hre, ← him]
  rw [hr, hi]
  rw [smul_neg]
  abel

#print axioms integral_complex_test_split
#print axioms WeakPartial.complex_test

end TheoremT.Continuum
