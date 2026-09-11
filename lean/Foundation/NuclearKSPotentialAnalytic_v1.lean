import NuclearKSPotential_v1
import CollisionFreeCutoff_v1
import KSMapAnalytic_v1

noncomputable section
open scoped ContDiff BigOperators
namespace TheoremT.Continuum

theorem coulombWithoutSelectedNucleus_contDiffAt_omega {N : ℕ} (i : Fin N) (Z : ℝ)
    {x : Configuration N} (hn : ∀ j : Fin N, j ≠ i → position x j ≠ 0)
    (hp : ∀ j k : Fin N, j ≠ k → position x j ≠ position x k) :
    ContDiffAt ℝ ω (coulombWithoutSelectedNucleus i Z) x := by
  have hc (j : Fin N) : ContDiffAt ℝ ω (fun y : Configuration N => position y j) x := by
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

theorem nuclearKSPotential_contDiffAt_omega {N : ℕ} (i : Fin N) (Z E : ℝ)
    {q : NuclearKSSpace i} (hq : q ∈ nuclearKSCoefficientPatch i) :
    ContDiffAt ℝ ω (nuclearKSPotential i Z E) q := by
  have hp := (coulombWithoutSelectedNucleus_contDiffAt_omega i Z hq.1 hq.2).comp q
    (nuclearKSLift_contDiff_omega i).contDiffAt
  have hr : ContDiff ℝ ω (fun q : NuclearKSSpace i => ‖q.1‖^2) := (contDiff_norm_sq ℝ).comp contDiff_fst
  exact contDiffAt_const.add ((contDiffAt_const.mul hr.contDiffAt).mul (hp.sub contDiffAt_const))

theorem nuclearKSPotential_analyticAt {N : ℕ} (i : Fin N) (Z E : ℝ)
    {q : NuclearKSSpace i} (hq : q ∈ nuclearKSCoefficientPatch i) :
    AnalyticAt ℝ (nuclearKSPotential i Z E) q :=
  (nuclearKSPotential_contDiffAt_omega i Z E hq).analyticAt

#print axioms coulombWithoutSelectedNucleus_contDiffAt_omega
#print axioms nuclearKSPotential_contDiffAt_omega
#print axioms nuclearKSPotential_analyticAt
end TheoremT.Continuum
