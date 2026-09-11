import LocalSecondTestIntegrability_v1
import GrushinSpectatorWeight_v1
import NuclearKSLift_v1

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum

theorem nuclear_KS_weighted_second_test_integrable {N : ℕ} (i : Fin N)
    {φ : NuclearKSSpace i → ℝ} {u : NuclearKSSpace i → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hu : ∀ q ∈ tsupport φ, ContDiffAt ℝ ∞ u q) (v : SpectatorConfiguration i) :
    Integrable (fun q => (‖q.1‖^2*fderiv ℝ (fun z => fderiv ℝ φ z (0,v)) q (0,v)) • u q) volume := by
  let ψ : NuclearKSSpace i → ℝ := fun q => ‖q.1‖^2*φ q
  have hs : tsupport ψ ⊆ tsupport φ := tsupport_mul_subset_right
  have hI := local_second_test_smul_integrable (μ := volume)
    (ks_spectator_weight_contDiff.mul hφ) hc.mul_left (fun q hq => hu q (hs hq)) (0,v)
  simpa only [ks_spectator_weight_second_product hφ] using hI

theorem nuclear_KS_test_weighted_second_integrable {N : ℕ} (i : Fin N)
    {φ : NuclearKSSpace i → ℝ} {u : NuclearKSSpace i → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hu : ∀ q ∈ tsupport φ, ContDiffAt ℝ ∞ u q) (v : SpectatorConfiguration i) :
    Integrable (fun q => φ q • (‖q.1‖^2 • fderiv ℝ (fun z => fderiv ℝ u z (0,v)) q (0,v))) volume := by
  apply local_smooth_test_smul_integrable hφ hc
  intro q hq
  exact ks_spectator_weight_contDiff.contDiffAt.smul
    (local_contDiffAt_directional_derivative (local_contDiffAt_directional_derivative (hu q hq) (0,v)) (0,v))

#print axioms nuclear_KS_weighted_second_test_integrable
#print axioms nuclear_KS_test_weighted_second_integrable
end TheoremT.Continuum
