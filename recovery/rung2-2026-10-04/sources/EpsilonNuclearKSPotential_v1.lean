import NuclearKSPotentialSmooth_v1

/-! Exact coefficient for the physically dilated Coulomb equation.
The factor epsilon multiplies the entire Coulomb potential, including repulsion.
All algebraic statements allow real epsilon; positive dilation is a separate
physical hypothesis. The existing nuclear coefficient patch is retained. -/
noncomputable section
open scoped ContDiff
namespace TheoremT.Continuum

def epsilonNuclearKSPotential {N : ℕ} (i : Fin N) (ε Z E : ℝ)
    (q : NuclearKSSpace i) : ℝ :=
  ε * nuclearKSPotential i Z (ε * E) q

theorem nuclearKSPotential_energy_affine {N : ℕ} (i : Fin N)
    (Z E : ℝ) (q : NuclearKSSpace i) :
    nuclearKSPotential i Z E q = nuclearKSPotential i Z 0 q - 8 * E * ‖q.1‖^2 := by
  dsimp [nuclearKSPotential]
  ring

theorem epsilonNuclearKSPotential_energy_affine {N : ℕ} (i : Fin N)
    (ε Z E : ℝ) (q : NuclearKSSpace i) :
    epsilonNuclearKSPotential i ε Z E q =
      ε * nuclearKSPotential i Z 0 q - 8 * ε^2 * E * ‖q.1‖^2 := by
  rw [epsilonNuclearKSPotential, nuclearKSPotential_energy_affine]
  ring

theorem epsilonNuclearKSPotential_eq_coulomb_scaled {N : ℕ} (i : Fin N)
    (ε Z E : ℝ) (q : NuclearKSSpace i) (hq : q.1 ≠ 0) :
    epsilonNuclearKSPotential i ε Z E q =
      8 * ‖q.1‖^2 * (ε * coulombPotential N Z (nuclearKSLift i q) - ε^2 * E) := by
  rw [epsilonNuclearKSPotential, nuclearKSPotential_eq_coulomb_scaled i Z (ε * E) q hq]
  ring

theorem epsilonNuclearKSPotential_on_zero {N : ℕ} (i : Fin N)
    (ε Z E : ℝ) (s : SpectatorConfiguration i) :
    epsilonNuclearKSPotential i ε Z E (0,s) = -8 * ε * Z := by
  rw [epsilonNuclearKSPotential, nuclearKSPotential_on_zero]
  ring

theorem epsilonNuclearKSPotential_contDiffAt {N : ℕ} (i : Fin N)
    (ε Z E : ℝ) {q : NuclearKSSpace i} (hq : q ∈ nuclearKSCoefficientPatch i) :
    ContDiffAt ℝ ∞ (epsilonNuclearKSPotential i ε Z E) q :=
  contDiffAt_const.mul (nuclearKSPotential_contDiffAt i Z (ε * E) hq)

end TheoremT.Continuum
