import CoulombPotentialSmoothAway_v1
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

noncomputable section
open scoped ContDiff
namespace TheoremT.Continuum

theorem collisionFree_isOpen (N : ℕ) : IsOpen {x : Configuration N | collisionFree x} := by
  have hp (i : Fin N) : Continuous (fun x : Configuration N => position x i) := by
    simpa only [← electronPositionCLM_apply] using (electronPositionCLM i).continuous
  have hn : IsOpen {x : Configuration N | ∀ i, position x i ≠ 0} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite (fun i => (isClosed_eq (hp i) continuous_const).isOpen_compl)
  have he : IsOpen {x : Configuration N | ∀ i j, i ≠ j → position x i ≠ position x j} := by
    simp only [Set.setOf_forall]
    apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro j
    apply isOpen_iInter_of_finite
    intro hij
    exact (isClosed_eq (hp i) (hp j)).isOpen_compl
  exact hn.inter he

theorem collisionFree_exists_smooth_cutoff {N : ℕ} {x : Configuration N}
    (hx : collisionFree x) :
    ∃ r : ℝ, 0 < r ∧ ∃ χ : Configuration N → ℝ,
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ y ∈ tsupport χ, collisionFree y) ∧
      ∀ y ∈ Metric.ball x r, χ y=1 := by
  obtain ⟨ε,hε,hs⟩ := Metric.isOpen_iff.mp (collisionFree_isOpen N) x hx
  let b : ContDiffBump x := ⟨ε/4,ε/2,by positivity,by linarith⟩
  refine ⟨ε/4,by positivity,b,b.contDiff,b.hasCompactSupport,?_,?_⟩
  · intro y hy
    apply hs
    have hy' : y ∈ Metric.closedBall x b.rOut := by
      simpa only [b.tsupport_eq] using hy
    change dist y x ≤ ε/2 at hy'
    exact lt_of_le_of_lt hy' (by linarith)
  · intro y hy
    exact b.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)

#print axioms collisionFree_exists_smooth_cutoff
end TheoremT.Continuum
