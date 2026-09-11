import HardyRankOneComplement_v1

/-! Conditional Temple enclosures from a single rank-one form comparison.
The full complement estimate is derived, not assumed again. -/
noncomputable section
open scoped InnerProductSpace LinearPMap
namespace TheoremT.OperatorTheory
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem unbounded_temple_of_rankOne_comparison (A : H →ₗ.[ℂ] H)
    (hsym : A.IsFormalAdjoint A) (l : H →L[ℂ] ℂ) (C β : ℝ)
    (hbound : ∀ x : A.domain, β * ‖(x : H)‖^2 ≤
      (inner ℂ (x : H) (A x)).re + C * ‖l (x : H)‖^2)
    (g : A.domain) (hg : ‖(g : H)‖ = 1) (E : ℝ)
    (hEg : A g = (E : ℂ) • (g : H)) (hgap : E < β)
    (ψ : A.domain) (hψ : ‖(ψ : H)‖ = 1)
    (hμ : (inner ℂ (ψ : H) (A ψ)).re < β) :
    let μ := (inner ℂ (ψ : H) (A ψ)).re
    μ - ‖A ψ - (μ : ℂ) • (ψ : H)‖^2 / (β - μ) ≤ E ∧ E ≤ μ :=
  unbounded_temple A hsym g hg E β hEg hgap
    (fun w hw => rankOne_ground_complement A hsym l C β hbound g hg E hEg hgap w hw)
    ψ hψ hμ

theorem unbounded_temple_directed_of_rankOne_comparison (A : H →ₗ.[ℂ] H)
    (hsym : A.IsFormalAdjoint A) (l : H →L[ℂ] ℂ) (C β : ℝ)
    (hbound : ∀ x : A.domain, β * ‖(x : H)‖^2 ≤
      (inner ℂ (x : H) (A x)).re + C * ‖l (x : H)‖^2)
    (g : A.domain) (hg : ‖(g : H)‖ = 1) (E : ℝ)
    (hEg : A g = (E : ℂ) • (g : H)) (hgap : E < β)
    (ψ : A.domain) (hψ : ‖(ψ : H)‖ = 1) (L U r : ℝ)
    (hL : L ≤ (inner ℂ (ψ : H) (A ψ)).re)
    (hU : (inner ℂ (ψ : H) (A ψ)).re ≤ U) (hUβ : U < β)
    (hr : ‖A ψ - ((inner ℂ (ψ : H) (A ψ)).re : ℂ) • (ψ : H)‖^2 ≤ r) :
    L - r / (β - U) ≤ E ∧ E ≤ U :=
  unbounded_temple_directed_enclosure A hsym g hg E β hEg hgap
    (fun w hw => rankOne_ground_complement A hsym l C β hbound g hg E hEg hgap w hw)
    ψ hψ L U r hL hU hUβ hr

/-- The below-separator eigenspace is one dimensional in the precise sense
that every eigenvector at E is a complex multiple of the given unit g.
This is not uniqueness of a normalized vector without its phase. -/
theorem ground_complement_eigenspace_rank_one (A : H →ₗ.[ℂ] H)
    (g : A.domain) (hg : ‖(g : H)‖ = 1) (E β : ℝ)
    (hEg : A g = (E : ℂ) • (g : H)) (hgap : E < β)
    (hcomp : ∀ w : A.domain, inner ℂ (g : H) (w : H) = 0 →
      β * ‖(w : H)‖^2 ≤ (inner ℂ (w : H) (A w)).re)
    (u : A.domain) (hEu : A u = (E : ℂ) • (u : H)) :
    (u : H) = inner ℂ (g : H) (u : H) • (g : H) := by
  let α := inner ℂ (g : H) (u : H)
  let w : A.domain := u - α • g
  have hwval : (w : H) = (u : H) - α • (g : H) := rfl
  have hgg : inner ℂ (g : H) (g : H) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hg]
    norm_num
  have hgw : inner ℂ (g : H) (w : H) = 0 := by
    rw [hwval, inner_sub_right, inner_smul_right, hgg]
    change α - α * 1 = 0
    ring
  have hAw : A w = (E : ℂ) • (w : H) := by
    simp only [w, A.map_sub, A.map_smul, hEu, hEg, Submodule.coe_sub, Submodule.coe_smul]
    module
  have hb := hcomp w hgw
  rw [hAw, inner_smul_right, inner_self_eq_norm_sq_to_K] at hb
  have hb' : β * ‖(w : H)‖^2 ≤ E * ‖(w : H)‖^2 := by
    simpa [Complex.mul_re, ← Complex.ofReal_pow] using hb
  have hz : ‖(w : H)‖^2 = 0 := by nlinarith [sq_nonneg ‖(w : H)‖]
  have hwzero : (w : H) = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
  exact sub_eq_zero.mp hwzero

#print axioms unbounded_temple_of_rankOne_comparison
#print axioms unbounded_temple_directed_of_rankOne_comparison
#print axioms ground_complement_eigenspace_rank_one
end TheoremT.OperatorTheory
