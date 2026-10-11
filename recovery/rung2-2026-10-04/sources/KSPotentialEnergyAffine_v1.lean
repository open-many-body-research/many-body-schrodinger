import EpsilonNuclearKSPotential_v1
import EpsilonPairKSPotential_v1

/-! Exact affine dependence on the scaled physical energy. These identities
retain the full unscaled interaction coefficient inside b_epsilon; the
physical scaled operator uses epsilon times this b_epsilon. -/
noncomputable section
open scoped ContDiff
namespace TheoremT.Continuum

theorem nuclearKSPotential_scaled_energy_affine_fun {N : ℕ} (i : Fin N) (Z E ε : ℝ) :
    nuclearKSPotential i Z (ε*E) =
      fun q => nuclearKSPotential i Z 0 q + ε * (-8*E*‖q.1‖^2) := by
  funext q
  rw [nuclearKSPotential_energy_affine]
  ring

theorem pairKSPotential_scaled_energy_affine_fun (Z E ε : ℝ) :
    pairKSPotential Z (ε*E) =
      fun q => pairKSPotential Z 0 q + ε * (-4*E*‖q.1‖^2) := by
  funext q
  rw [pairKSPotential_energy_affine]
  ring

theorem nuclearKS_energy_coefficient_contDiff {N : ℕ} (i : Fin N) (E : ℝ) :
    ContDiff ℝ ∞ (fun q : NuclearKSSpace i => -8*E*‖q.1‖^2) := by
  have h : ContDiff ℝ ∞ (fun q : NuclearKSSpace i => ‖q.1‖^2) :=
    (contDiff_norm_sq ℝ).comp contDiff_fst
  exact contDiff_const.mul h

theorem pairKS_energy_coefficient_contDiff (E : ℝ) :
    ContDiff ℝ ∞ (fun q : PairKSSpace => -4*E*‖q.1‖^2) := by
  have h : ContDiff ℝ ∞ (fun q : PairKSSpace => ‖q.1‖^2) :=
    (contDiff_norm_sq ℝ).comp contDiff_fst
  exact contDiff_const.mul h

#print axioms nuclearKSPotential_scaled_energy_affine_fun
#print axioms pairKSPotential_scaled_energy_affine_fun
#print axioms nuclearKS_energy_coefficient_contDiff
#print axioms pairKS_energy_coefficient_contDiff
end TheoremT.Continuum
