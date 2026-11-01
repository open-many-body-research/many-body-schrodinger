import PairKSPotentialSmooth_v1

/-! Exact epsilon-scaled pair-chart coefficient, including epsilon times the
repulsive pair constant. The physical unscaled center gives Grushin c=1;
this coefficient scaling does not change that principal part. -/
noncomputable section
open scoped ContDiff
namespace TheoremT.Continuum

def epsilonPairKSPotential (ε Z E : ℝ) (q : PairKSSpace) : ℝ :=
  ε * pairKSPotential Z (ε * E) q

theorem pairKSPotential_energy_affine (Z E : ℝ) (q : PairKSSpace) :
    pairKSPotential Z E q = pairKSPotential Z 0 q - 4 * E * ‖q.1‖^2 := by
  dsimp [pairKSPotential]
  ring

theorem epsilonPairKSPotential_energy_affine (ε Z E : ℝ) (q : PairKSSpace) :
    epsilonPairKSPotential ε Z E q =
      ε * pairKSPotential Z 0 q - 4 * ε^2 * E * ‖q.1‖^2 := by
  rw [epsilonPairKSPotential, pairKSPotential_energy_affine]
  ring

theorem epsilonPairKSPotential_eq_coulomb_scaled (ε Z E : ℝ)
    (q : PairKSSpace) (hq : q.1 ≠ 0) :
    epsilonPairKSPotential ε Z E q =
      4 * ‖q.1‖^2 * (ε * coulombPotential 2 Z (pairKSLift q) - ε^2 * E) := by
  rw [epsilonPairKSPotential, pairKSPotential_eq_coulomb_scaled Z (ε * E) q hq]
  ring

theorem epsilonPairKSPotential_on_zero (ε Z E : ℝ)
    (s : SpectatorConfiguration (0 : Fin 2)) :
    epsilonPairKSPotential ε Z E (0,s) = 4 * ε := by
  rw [epsilonPairKSPotential, pairKSPotential_on_zero]
  ring

theorem epsilonPairKSPotential_contDiffAt (ε Z E : ℝ)
    {q : PairKSSpace} (hq : q ∈ pairKSCoefficientPatch) :
    ContDiffAt ℝ ∞ (epsilonPairKSPotential ε Z E) q :=
  contDiffAt_const.mul (pairKSPotential_contDiffAt Z (ε * E) hq)

end TheoremT.Continuum
