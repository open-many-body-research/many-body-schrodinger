import PairKSLift_v1
import TwoElectronRelativeCoordinates_v1

/-! Physical image norms for the unchanged nuclear and pair KS charts.
The pair center is t and the relative position is KS(y), with no rescaling
by sqrt(2). The fixed bounds below contain the real initialization boxes. -/
noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum

theorem nuclearKSLift_norm_sq {N : ℕ} (i : Fin N) (q : NuclearKSSpace i) :
    ‖nuclearKSLift i q‖^2 = ‖q.1‖^4 + ‖q.2‖^2 := by
  change ‖(configurationSplit i).symm (WithLp.toLp 2 (ksMap q.1,q.2))‖^2 = _
  rw [(configurationSplit i).symm.norm_map,WithLp.prod_norm_sq_eq_of_L2]
  change ‖ksMap q.1‖^2 + ‖q.2‖^2 = _
  rw [ksMap_norm]
  ring

theorem pairKSLift_norm_sq (q : PairKSSpace) :
    ‖pairKSLift q‖^2 = 2 * ‖q.2‖^2 + ‖q.1‖^4 / 2 := by
  have h : ‖pairKSLift q‖^2 =
      2 * ‖pairCenterEquiv q.2‖^2 + ‖ksMap q.1‖^2 / 2 := by
    rw [configuration_two_norm_sq,EuclideanSpace.real_norm_sq_eq,
      EuclideanSpace.real_norm_sq_eq]
    simp only [Finset.mul_sum,Finset.sum_div,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    change (pairCenterEquiv q.2 k + ksMap q.1 k / 2)^2 +
      (pairCenterEquiv q.2 k + -(ksMap q.1 k / 2))^2 =
      2 * (pairCenterEquiv q.2 k)^2 + (ksMap q.1 k)^2 / 2
    ring
  rw [h,pairCenterEquiv.norm_map,ksMap_norm]
  ring

theorem nuclearKSLift_norm_lt_two {N : ℕ} (i : Fin N) (q : NuclearKSSpace i)
    (hy : ‖q.1‖ ≤ (1/4 : ℝ)) (ht : ‖q.2‖ ≤ (5/4 : ℝ)) :
    ‖nuclearKSLift i q‖ < 2 := by
  have hy2 := pow_le_pow_left₀ (norm_nonneg q.1) hy 2
  have hy4 := pow_le_pow_left₀ (sq_nonneg ‖q.1‖) hy2 2
  have ht2 := pow_le_pow_left₀ (norm_nonneg q.2) ht 2
  have hnorm := nuclearKSLift_norm_sq i q
  nlinarith [norm_nonneg (nuclearKSLift i q)]

theorem pairKSLift_norm_lt_two (q : PairKSSpace)
    (hy : ‖q.1‖ ≤ (1/4 : ℝ)) (ht : ‖q.2‖ ≤ (5/4 : ℝ)) :
    ‖pairKSLift q‖ < 2 := by
  have hy2 := pow_le_pow_left₀ (norm_nonneg q.1) hy 2
  have hy4 := pow_le_pow_left₀ (sq_nonneg ‖q.1‖) hy2 2
  have ht2 := pow_le_pow_left₀ (norm_nonneg q.2) ht 2
  have hnorm := pairKSLift_norm_sq q
  nlinarith [norm_nonneg (pairKSLift q)]

#print axioms nuclearKSLift_norm_sq
#print axioms pairKSLift_norm_sq
#print axioms nuclearKSLift_norm_lt_two
#print axioms pairKSLift_norm_lt_two
end TheoremT.Continuum
