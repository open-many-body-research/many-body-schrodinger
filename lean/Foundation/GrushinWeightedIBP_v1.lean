import LocalSecondDerivativeIBP_v1
import GrushinSpectatorWeight_v1
import NuclearKSLift_v1
import NuclearKSVolumeHaar_v1

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum

theorem nuclear_KS_weighted_spectator_integration_by_parts {N : ℕ} (i : Fin N)
    {φ : NuclearKSSpace i → ℝ} {u : NuclearKSSpace i → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hu : ∀ q ∈ tsupport φ, ContDiffAt ℝ ∞ u q) (v : SpectatorConfiguration i) :
    (∫ q, (‖q.1‖^2*fderiv ℝ (fun z => fderiv ℝ φ z (0,v)) q (0,v)) • u q) =
      ∫ q, φ q • (‖q.1‖^2 • fderiv ℝ (fun z => fderiv ℝ u z (0,v)) q (0,v)) := by
  letI := nuclearKS_volume_isAddHaar i
  let ψ : NuclearKSSpace i → ℝ := fun q => ‖q.1‖^2*φ q
  have hs : tsupport ψ ⊆ tsupport φ := tsupport_mul_subset_right
  have hh := local_second_directional_integration_by_parts
    (μ := (volume : Measure (NuclearKSSpace i))) (ks_spectator_weight_contDiff.mul hφ)
    hc.mul_left (fun q hq => hu q (hs hq)) (0,v)
  simp only [ks_spectator_weight_second_product hφ] at hh
  rw [hh]
  apply integral_congr_ae
  filter_upwards [] with q
  rw [mul_smul,smul_comm]

#print axioms nuclear_KS_weighted_spectator_integration_by_parts
end TheoremT.Continuum
