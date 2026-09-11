import CoulombCuspLocallyLipschitz_v1
import Mathlib.Analysis.InnerProductSpace.Calculus

noncomputable section
open scoped ContDiff BigOperators
namespace TheoremT.Continuum

theorem coulombPotential_contDiffAt_collisionFree {N : ℕ} (Z : ℝ)
    {x : Configuration N} (hx : collisionFree x) :
    ContDiffAt ℝ ∞ (coulombPotential N Z) x := by
  have hp (i : Fin N) : ContDiffAt ℝ ∞ (fun y : Configuration N => position y i) x := by
    simpa only [← electronPositionCLM_apply] using (electronPositionCLM i).contDiff.contDiffAt
  have hn (i : Fin N) : ContDiffAt ℝ ∞ (fun y : Configuration N => ‖position y i‖⁻¹) x :=
    ((hp i).norm ℝ (hx.1 i)).inv (norm_ne_zero_iff.mpr (hx.1 i))
  have he (i j : Fin N) (hij : i ≠ j) :
      ContDiffAt ℝ ∞ (fun y : Configuration N => ‖position y i-position y j‖⁻¹) x :=
    (((hp i).sub (hp j)).norm ℝ (sub_ne_zero.mpr (hx.2 i j hij))).inv
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hx.2 i j hij)))
  apply ContDiffAt.add
  · exact contDiffAt_const.mul (ContDiffAt.sum (fun i _ => hn i))
  · apply ContDiffAt.sum
    intro i hi
    apply ContDiffAt.sum
    intro j hj
    exact he i j (ne_of_lt (Finset.mem_filter.mp hj).2)

#print axioms coulombPotential_contDiffAt_collisionFree
end TheoremT.Continuum
