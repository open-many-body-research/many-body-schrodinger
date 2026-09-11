import CoulombPotentialSmoothAway_v1
import Mathlib.Analysis.Calculus.FDeriv.Congr

noncomputable section
open scoped ContDiff Topology
namespace TheoremT.Continuum

theorem smooth_mul_of_smooth_on_tsupport {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {χ V : E → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hV : ∀ x ∈ tsupport χ, ContDiffAt ℝ ∞ V x) :
    ContDiff ℝ ∞ (fun x => χ x*V x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport χ
  · exact hχ.contDiffAt.mul (hV x hx)
  · apply contDiffAt_const.congr_of_eventuallyEq (f := fun _ => (0:ℝ))
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    simp [hy]

theorem localized_coulomb_coefficient_smooth {N : ℕ} (Z E : ℝ)
    {χ : Configuration N → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hs : ∀ x ∈ tsupport χ, collisionFree x) :
    ContDiff ℝ ∞ (fun x => χ x*(2*(coulombPotential N Z x-E))) := by
  apply smooth_mul_of_smooth_on_tsupport hχ
  intro x hx
  exact contDiffAt_const.mul ((coulombPotential_contDiffAt_collisionFree Z (hs x hx)).sub contDiffAt_const)

theorem localized_coulomb_coefficient_compact {N : ℕ} (Z E : ℝ)
    {χ : Configuration N → ℝ} (hc : HasCompactSupport χ) :
    HasCompactSupport (fun x => χ x*(2*(coulombPotential N Z x-E))) := hc.mul_right

#print axioms localized_coulomb_coefficient_smooth
end TheoremT.Continuum
