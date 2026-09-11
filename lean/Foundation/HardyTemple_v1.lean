import HardyTempleDecomposition_v1

/-! Temple's residual enclosure on the actual domain of a possibly unbounded
symmetric operator. This remains a conditional formal implication until its
specified physical eigenpair and complement lower bound are established.
Neither D(A²), self-adjointness, finite dimension, nor moment identities are
assumed in this theorem. -/
noncomputable section
open scoped InnerProductSpace LinearPMap
namespace TheoremT.OperatorTheory
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Actual-domain rank-one Temple inequality. The expectation is the literal
real inner product with Aψ, and the residual is the literal Hilbert norm. -/
theorem unbounded_temple (A : H →ₗ.[ℂ] H) (hsym : A.IsFormalAdjoint A)
    (g : A.domain) (hg : ‖(g : H)‖ = 1) (E β : ℝ)
    (hEg : A g = (E : ℂ) • (g : H)) (hgap : E < β)
    (hcomp : ∀ w : A.domain, inner ℂ (g : H) (w : H) = 0 →
      β * ‖(w : H)‖^2 ≤ (inner ℂ (w : H) (A w)).re)
    (ψ : A.domain) (hψ : ‖(ψ : H)‖ = 1)
    (hμ : (inner ℂ (ψ : H) (A ψ)).re < β) :
    (inner ℂ (ψ : H) (A ψ)).re -
        ‖A ψ - ((inner ℂ (ψ : H) (A ψ)).re : ℂ) • (ψ : H)‖^2 /
          (β - (inner ℂ (ψ : H) (A ψ)).re) ≤ E ∧
      E ≤ (inner ℂ (ψ : H) (A ψ)).re := by
  obtain ⟨ht, hshift⟩ := ground_complement_shift_estimate A hsym g hg E β hEg hgap hcomp ψ hψ
  have hv := unit_variance_shift_identity (ψ : H) (A ψ) hψ E
  rw [hv] at hshift
  have hres : ((inner ℂ (ψ : H) (A ψ)).re - E) *
      (β - (inner ℂ (ψ : H) (A ψ)).re) ≤
      ‖A ψ - ((inner ℂ (ψ : H) (A ψ)).re : ℂ) • (ψ : H)‖^2 := by
    nlinarith
  have hdiv := (le_div_iff₀ (sub_pos.mpr hμ)).mpr hres
  constructor <;> linarith

/-- A form suitable for separately certified directed bounds: L≤μ≤U and
residual²≤r yield an enclosure using the positive denominator β−U. This is
an implication about certificates, not a procedure that computes them. -/
theorem unbounded_temple_directed_enclosure (A : H →ₗ.[ℂ] H)
    (hsym : A.IsFormalAdjoint A) (g : A.domain) (hg : ‖(g : H)‖ = 1)
    (E β : ℝ) (hEg : A g = (E : ℂ) • (g : H)) (hgap : E < β)
    (hcomp : ∀ w : A.domain, inner ℂ (g : H) (w : H) = 0 →
      β * ‖(w : H)‖^2 ≤ (inner ℂ (w : H) (A w)).re)
    (ψ : A.domain) (hψ : ‖(ψ : H)‖ = 1) (L U r : ℝ)
    (hL : L ≤ (inner ℂ (ψ : H) (A ψ)).re)
    (hU : (inner ℂ (ψ : H) (A ψ)).re ≤ U) (hUβ : U < β)
    (hr : ‖A ψ - ((inner ℂ (ψ : H) (A ψ)).re : ℂ) • (ψ : H)‖^2 ≤ r) :
    L - r / (β - U) ≤ E ∧ E ≤ U := by
  have ht := unbounded_temple A hsym g hg E β hEg hgap hcomp ψ hψ (hU.trans_lt hUβ)
  have hden : 0 < β - U := sub_pos.mpr hUβ
  have hμden : 0 < β - (inner ℂ (ψ : H) (A ψ)).re := sub_pos.mpr (hU.trans_lt hUβ)
  have hratio :
      ‖A ψ - ((inner ℂ (ψ : H) (A ψ)).re : ℂ) • (ψ : H)‖^2 /
          (β - (inner ℂ (ψ : H) (A ψ)).re) ≤ r / (β - U) := by
    exact div_le_div₀ ((sq_nonneg _).trans hr) hr hden (sub_le_sub_left hU β)
  exact ⟨le_trans (by linarith) ht.1, ht.2.trans hU⟩

#print axioms unbounded_temple
#print axioms unbounded_temple_directed_enclosure
end TheoremT.OperatorTheory
