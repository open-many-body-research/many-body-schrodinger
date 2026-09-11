import GrushinTestSupport_v1
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section
open MeasureTheory
namespace TheoremT.Continuum

theorem nuclear_KS_real_test_mul_integrable {N : ℕ} (i : Fin N)
    {φ : NuclearKSSpace i → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ)
    {u : NuclearKSSpace i → ℂ} (hu : Continuous u) :
    Integrable (fun q => (φ q : ℂ)*u q) volume := by
  have hcc : HasCompactSupport (fun q => (φ q : ℂ)) :=
    hc.comp_left (g := fun r : ℝ => (r : ℂ)) rfl
  exact ((Complex.continuous_ofReal.comp hφ).mul hu).integrable_of_hasCompactSupport hcc.mul_right

#print axioms nuclear_KS_real_test_mul_integrable
end TheoremT.Continuum
