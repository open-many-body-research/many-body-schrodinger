import CollisionFreeCutoff_v1

noncomputable section
open Filter
open scoped ContDiff Topology
namespace TheoremT.Continuum

theorem open_exists_smooth_cutoff_at {N : ℕ} {Ω : Set (Configuration N)}
    (hΩ : IsOpen Ω) {x : Configuration N} (hx : x ∈ Ω) :
    ∃ r : ℝ, 0 < r ∧ ∃ χ : Configuration N → ℝ,
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ Ω ∧
      ∀ y ∈ Metric.ball x r, χ y=1 := by
  obtain ⟨ε,hε,hs⟩ := Metric.isOpen_iff.mp hΩ x hx
  let b : ContDiffBump x := ⟨ε/4,ε/2,by positivity,by linarith⟩
  refine ⟨ε/4,by positivity,b,b.contDiff,b.hasCompactSupport,?_,?_⟩
  · intro y hy
    apply hs
    have hy' : y ∈ Metric.closedBall x b.rOut := by simpa only [b.tsupport_eq] using hy
    change dist y x ≤ ε/2 at hy'
    exact lt_of_le_of_lt hy' (by linarith)
  · intro y hy
    exact b.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)

#print axioms open_exists_smooth_cutoff_at
end TheoremT.Continuum
