import NuclearKSPotential_v1
import CollisionFreeCutoff_v1

noncomputable section
open scoped ContDiff BigOperators
namespace TheoremT.Continuum

theorem coulombWithoutSelectedNucleus_contDiffAt {N : ℕ} (i : Fin N) (Z : ℝ)
    {x : Configuration N} (hn : ∀ j : Fin N, j ≠ i → position x j ≠ 0)
    (hp : ∀ j k : Fin N, j ≠ k → position x j ≠ position x k) :
    ContDiffAt ℝ ∞ (coulombWithoutSelectedNucleus i Z) x := by
  have hc (j : Fin N) : ContDiffAt ℝ ∞ (fun y : Configuration N => position y j) x := by
    simpa only [← electronPositionCLM_apply] using (electronPositionCLM j).contDiff.contDiffAt
  apply ContDiffAt.add
  · apply contDiffAt_const.mul
    apply ContDiffAt.sum
    intro j hj
    exact ((hc j).norm ℝ (hn j (Finset.mem_erase.mp hj).1)).inv
      (norm_ne_zero_iff.mpr (hn j (Finset.mem_erase.mp hj).1))
  · apply ContDiffAt.sum
    intro j hj
    apply ContDiffAt.sum
    intro k hk
    have hne := hp j k (ne_of_lt (Finset.mem_filter.mp hk).2)
    exact (((hc j).sub (hc k)).norm ℝ (sub_ne_zero.mpr hne)).inv
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne))

theorem nuclearKSPotential_contDiffAt {N : ℕ} (i : Fin N) (Z E : ℝ)
    {q : NuclearKSSpace i} (hq : q ∈ nuclearKSCoefficientPatch i) :
    ContDiffAt ℝ ∞ (nuclearKSPotential i Z E) q := by
  have hp := (coulombWithoutSelectedNucleus_contDiffAt i Z hq.1 hq.2).comp q
    (nuclearKSLift_contDiff i).contDiffAt
  have hr : ContDiff ℝ ∞ (fun q : NuclearKSSpace i => ‖q.1‖^2) := (contDiff_norm_sq ℝ).comp contDiff_fst
  exact contDiffAt_const.add ((contDiffAt_const.mul hr.contDiffAt).mul (hp.sub contDiffAt_const))

theorem nuclearKSCoefficientPatch_isOpen {N : ℕ} (i : Fin N) : IsOpen (nuclearKSCoefficientPatch i) := by
  have hc (j : Fin N) : Continuous (fun q : NuclearKSSpace i => position (nuclearKSLift i q) j) :=
    (continuous_position j).comp (nuclearKSLift_contDiff i).continuous
  change IsOpen ({q : NuclearKSSpace i | ∀ j : Fin N, j ≠ i → position (nuclearKSLift i q) j ≠ 0} ∩
    {q : NuclearKSSpace i | ∀ j k : Fin N, j ≠ k → position (nuclearKSLift i q) j ≠ position (nuclearKSLift i q) k})
  apply IsOpen.inter
  · simp only [Set.setOf_forall]
    apply isOpen_iInter_of_finite
    intro j
    apply isOpen_iInter_of_finite
    intro hji
    exact (isClosed_eq (hc j) continuous_const).isOpen_compl
  · simp only [Set.setOf_forall]
    apply isOpen_iInter_of_finite
    intro j
    apply isOpen_iInter_of_finite
    intro k
    apply isOpen_iInter_of_finite
    intro hjk
    exact (isClosed_eq (hc j) (hc k)).isOpen_compl

#print axioms nuclearKSPotential_contDiffAt
#print axioms nuclearKSCoefficientPatch_isOpen
end TheoremT.Continuum
