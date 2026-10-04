import PairKSLift_v1
import CoulombTwoElectronExpectation_v1

/-! The actual two-electron pair KS coefficient, with the repulsive pair pole
removed by the exact factor four times the squared KS radius. Its coefficient
patch excludes both nuclear positions but includes pair collisions away from
the nucleus. No regularization of the physical potential is used. -/
noncomputable section
open scoped ContDiff BigOperators
namespace TheoremT.Continuum

def pairKSPotential (Z E : ℝ) (q : PairKSSpace) : ℝ :=
  4+4*‖q.1‖^2*(-Z*(‖position (pairKSLift q) 0‖⁻¹+
    ‖position (pairKSLift q) 1‖⁻¹)-E)

def pairKSCoefficientPatch : Set PairKSSpace :=
  {q | position (pairKSLift q) 0 ≠ 0 ∧ position (pairKSLift q) 1 ≠ 0}

theorem pairKSPotential_eq_coulomb_scaled (Z E : ℝ)
    (q : PairKSSpace) (hq : q.1 ≠ 0) :
    pairKSPotential Z E q = 4*‖q.1‖^2*(coulombPotential 2 Z (pairKSLift q)-E) := by
  rw [coulombPotential_two_electrons,pairKSLift_pair_radius]
  dsimp [pairKSPotential]
  field_simp [norm_ne_zero_iff.mpr hq]
  <;> ring

theorem pairKSPotential_on_zero (Z E : ℝ)
    (s : SpectatorConfiguration (0 : Fin 2)) : pairKSPotential Z E (0,s) = 4 := by
  simp [pairKSPotential]

theorem pairKSCoefficientPatch_off_zero_collisionFree
    {q : PairKSSpace} (hq : q ∈ pairKSCoefficientPatch) (hy : q.1 ≠ 0) :
    collisionFree (pairKSLift q) := by
  have hne : position (pairKSLift q) 0 ≠ position (pairKSLift q) 1 := by
    apply sub_ne_zero.mp
    rw [pairKSLift_difference]
    exact (ksMap_eq_zero_iff q.1).not.mpr hy
  refine ⟨?_,?_⟩
  · intro i
    fin_cases i
    · exact hq.1
    · exact hq.2
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · exact hne
    · exact hne.symm
    · exact False.elim (hij rfl)

#print axioms pairKSPotential_eq_coulomb_scaled
#print axioms pairKSPotential_on_zero
#print axioms pairKSCoefficientPatch_off_zero_collisionFree
end TheoremT.Continuum
