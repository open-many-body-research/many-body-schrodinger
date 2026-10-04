import PairKSPotential_v1
import CollisionFreeCutoff_v1

/-! Smoothness of the exact pair KS coefficient through the pair collision
on the open patch where both physical nuclear positions are nonzero. -/
noncomputable section
open scoped ContDiff BigOperators
namespace TheoremT.Continuum

theorem pairKSPotential_contDiffAt (Z E : ℝ)
    {q : PairKSSpace} (hq : q ∈ pairKSCoefficientPatch) :
    ContDiffAt ℝ ∞ (pairKSPotential Z E) q := by
  have hc (j : Fin 2) : ContDiffAt ℝ ∞
      (fun z : PairKSSpace => position (pairKSLift z) j) q := by
    have hp : ContDiff ℝ ∞ (fun x : Configuration 2 => position x j) := by
      simpa only [← electronPositionCLM_apply] using (electronPositionCLM j).contDiff
    exact (hp.comp pairKSLift_contDiff).contDiffAt
  have h0 := ((hc 0).norm ℝ hq.1).inv (norm_ne_zero_iff.mpr hq.1)
  have h1 := ((hc 1).norm ℝ hq.2).inv (norm_ne_zero_iff.mpr hq.2)
  have hr : ContDiff ℝ ∞ (fun z : PairKSSpace => ‖z.1‖^2) :=
    (contDiff_norm_sq ℝ).comp contDiff_fst
  exact contDiffAt_const.add ((contDiffAt_const.mul hr.contDiffAt).mul
    ((contDiffAt_const.mul (h0.add h1)).sub contDiffAt_const))

theorem pairKSCoefficientPatch_isOpen : IsOpen pairKSCoefficientPatch := by
  have hc (j : Fin 2) : Continuous (fun q : PairKSSpace => position (pairKSLift q) j) :=
    (continuous_position j).comp pairKSLift_contDiff.continuous
  change IsOpen ({q : PairKSSpace | position (pairKSLift q) 0 ≠ 0} ∩
    {q : PairKSSpace | position (pairKSLift q) 1 ≠ 0})
  exact (isClosed_eq (hc 0) continuous_const).isOpen_compl.inter
    (isClosed_eq (hc 1) continuous_const).isOpen_compl

#print axioms pairKSPotential_contDiffAt
#print axioms pairKSCoefficientPatch_isOpen
end TheoremT.Continuum
