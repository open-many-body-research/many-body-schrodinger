import NewtonFundamentalSolution_v1
import ReflectedTestDerivatives_v1

/-! Pointwise Newton representation of every real smooth compact function.
This is an identity with the actual kernel integral, not an abstract inverse. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum

theorem smooth_compact_newton_representation {N : ℕ} (hN : 0 < N)
    {φ : Configuration N → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (x : Configuration N) :
    (∫ y, normalizedNewtonPotential N y*realTestLaplacian φ (x-y))=φ x := by
  have ht : ContDiff ℝ ∞ (fun y => φ (x-y)) := hφ.comp (contDiff_const.sub contDiff_id)
  have hct : HasCompactSupport (fun y => φ (x-y)) := hc.comp_homeomorph (Homeomorph.subLeft x)
  have hh := normalizedNewtonPotential_fundamental_solution hN ht hct
  simpa only [reflected_real_test_laplacian hφ,sub_zero,mul_comm] using hh

#print axioms smooth_compact_newton_representation
end TheoremT.Continuum
