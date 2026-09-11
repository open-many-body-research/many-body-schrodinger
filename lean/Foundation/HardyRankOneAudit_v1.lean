import HardyRankOneTemple_v1

/-! Expanded conditional rank-one comparison/complement/Temple statements.
The comparison is a genuine quadratic-form inequality on every domain
vector; it is not supplied as the intended complement conclusion. -/
noncomputable section
open scoped InnerProductSpace LinearPMap
set_option pp.proofs false
set_option pp.maxSteps 200000
namespace TheoremT.OperatorTheory.RankOneAudit
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem exact_comparison_to_complement (A : H →ₗ.[ℂ] H)
    (hsym : ∀ x y : A.domain, inner ℂ (A x) (y : H) = inner ℂ (x : H) (A y))
    (l : H →L[ℂ] ℂ) (C β : ℝ)
    (hbound : ∀ x : A.domain, β * ‖(x : H)‖^2 ≤
      (inner ℂ (x : H) (A x)).re + C * ‖l (x : H)‖^2)
    (g : A.domain) (hg : ‖(g : H)‖ = 1) (E : ℝ)
    (hEg : A g = (E : ℂ) • (g : H)) (hgap : E < β) :
    l (g : H) ≠ 0 ∧ ∀ w : A.domain,
      inner ℂ (g : H) (w : H) = 0 →
      β * ‖(w : H)‖^2 ≤ (inner ℂ (w : H) (A w)).re :=
  ⟨rankOne_ground_functional_ne_zero A l C β hbound g hg E hEg hgap,
    fun w hw => rankOne_ground_complement A hsym l C β hbound g hg E hEg hgap w hw⟩

theorem normalized_ground_unique_up_to_phase (A : H →ₗ.[ℂ] H)
    (g : A.domain) (hg : ‖(g : H)‖ = 1) (E β : ℝ)
    (hEg : A g = (E : ℂ) • (g : H)) (hgap : E < β)
    (hcomp : ∀ w : A.domain, inner ℂ (g : H) (w : H) = 0 →
      β * ‖(w : H)‖^2 ≤ (inner ℂ (w : H) (A w)).re)
    (u : A.domain) (hu : ‖(u : H)‖ = 1) (hEu : A u = (E : ℂ) • (u : H)) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ (u : H) = c • (g : H) := by
  have hs := ground_complement_eigenspace_rank_one A g hg E β hEg hgap hcomp u hEu
  refine ⟨inner ℂ (g : H) (u : H), ?_, hs⟩
  have hn := congrArg norm hs
  rw [hu, _root_.norm_smul, hg, mul_one] at hn
  exact hn.symm

#print exact_comparison_to_complement
#print normalized_ground_unique_up_to_phase
#print TheoremT.OperatorTheory.rankOne_ground_complement_weighted
#print TheoremT.OperatorTheory.unbounded_temple_of_rankOne_comparison
#print TheoremT.OperatorTheory.unbounded_temple_directed_of_rankOne_comparison
#print TheoremT.OperatorTheory.ground_complement_eigenspace_rank_one
#print axioms exact_comparison_to_complement
#print axioms normalized_ground_unique_up_to_phase
#print axioms TheoremT.OperatorTheory.unbounded_temple_of_rankOne_comparison
#print axioms TheoremT.OperatorTheory.unbounded_temple_directed_of_rankOne_comparison
end TheoremT.OperatorTheory.RankOneAudit
