import ContinuumFoundation_v1
import Mathlib.Analysis.Distribution.TemperedDistribution

/-!
Bridge from a tempered-distribution derivative identity to the project's
actual WeakPartial predicate with all real compact smooth test functions.
This proves only the stated reverse direction; it does not assume or establish
the converse extension from compact tests to Schwartz tests.
-/

noncomputable section

open MeasureTheory LineDeriv
open scoped SchwartzMap ContDiff

namespace TheoremT.Continuum

/-- A distributional derivative represented by g satisfies the exact original
real-test WeakPartial predicate. There is no Sobolev regularity premise. -/
theorem weakPartial_of_temperedDistribution_derivative
    {N : ℕ} {f g : SpatialL2 N} {k : Coordinate N}
    (h : ∂_{coordinateVector k} (f : 𝓢'(Configuration N, ℂ)) =
      (g : 𝓢'(Configuration N, ℂ))) :
    WeakPartial f g k := by
  intro φ hφ hcφ
  have hc : HasCompactSupport (Complex.ofRealCLM ∘ φ) := hcφ.comp_left rfl
  have hd : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ φ) := by fun_prop
  let φS : 𝓢(Configuration N, ℂ) := hc.toSchwartzMap hd
  have hderiv (x : Configuration N) :
      (∂_{coordinateVector k} φS) x =
        (fderiv ℝ φ x (coordinateVector k) : ℂ) := by
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    change fderiv ℝ (Complex.ofRealCLM ∘ φ) x (coordinateVector k) = _
    rw [fderiv_comp x Complex.ofRealCLM.differentiableAt
      (hφ.differentiable (by norm_num) x)]
    simp
  calc
    (∫ x, φ x • g x) = (g : 𝓢'(Configuration N, ℂ)) φS := by
      simp [φS, Lp.toTemperedDistribution_apply]
    _ = (∂_{coordinateVector k} (f : 𝓢'(Configuration N, ℂ))) φS := by rw [h]
    _ = -(∫ x, fderiv ℝ φ x (coordinateVector k) • f x) := by
      simp [TemperedDistribution.lineDerivOp_apply_apply,
        Lp.toTemperedDistribution_apply, hderiv, integral_neg]

#print axioms weakPartial_of_temperedDistribution_derivative

end TheoremT.Continuum
