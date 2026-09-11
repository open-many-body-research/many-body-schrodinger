import HardyTemple_v1
import HardyCoulombTemple_v1

/-! Expanded conditional statements for the actual unbounded Temple theorem.
The physical eigenvector and full orthogonal complement estimate remain
visible hypotheses. No finite matrix, spectral measure, A² moment, or
ionization-threshold substitution is used. -/
noncomputable section
open scoped InnerProductSpace LinearPMap
set_option pp.proofs false
set_option pp.maxSteps 200000
namespace TheoremT.OperatorTheory.TempleAudit
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem exact_unbounded_statement (A : H →ₗ.[ℂ] H)
    (hsym : ∀ x y : A.domain,
      inner ℂ (A x) (y : H) = inner ℂ (x : H) (A y))
    (g ψ : A.domain) (hg : ‖(g : H)‖ = 1) (hψ : ‖(ψ : H)‖ = 1)
    (E β : ℝ) (hEg : A g = (E : ℂ) • (g : H)) (hgap : E < β)
    (hcomp : ∀ w : A.domain, inner ℂ (g : H) (w : H) = 0 →
      β * ‖(w : H)‖^2 ≤ (inner ℂ (w : H) (A w)).re)
    (hμ : (inner ℂ (ψ : H) (A ψ)).re < β) :
    (inner ℂ (ψ : H) (A ψ)).re -
      ‖A ψ - ((inner ℂ (ψ : H) (A ψ)).re : ℂ) • (ψ : H)‖^2 /
        (β - (inner ℂ (ψ : H) (A ψ)).re) ≤ E ∧
      E ≤ (inner ℂ (ψ : H) (A ψ)).re :=
  unbounded_temple A hsym g hg E β hEg hgap hcomp ψ hψ hμ

/-- The complement hypothesis also proves that E really is the minimum of
the normalized domain Rayleigh values; 'ground' is not an additional label
assumed in order to prove the generic result. -/
theorem exact_rayleigh_minimum (A : H →ₗ.[ℂ] H) (hsym : A.IsFormalAdjoint A)
    (g : A.domain) (hg : ‖(g : H)‖ = 1) (E β : ℝ)
    (hEg : A g = (E : ℂ) • (g : H)) (hgap : E < β)
    (hcomp : ∀ w : A.domain, inner ℂ (g : H) (w : H) = 0 →
      β * ‖(w : H)‖^2 ≤ (inner ℂ (w : H) (A w)).re) :
    IsLeast {e : ℝ | ∃ ψ : A.domain,
      ‖(ψ : H)‖ = 1 ∧ e = (inner ℂ (ψ : H) (A ψ)).re} E := by
  constructor
  · refine ⟨g, hg, ?_⟩
    rw [hEg, inner_smul_right, inner_self_eq_norm_sq_to_K, hg]
    simp
  · rintro e ⟨ψ, hψ, rfl⟩
    exact sub_nonneg.mp (ground_complement_shift_estimate A hsym g hg E β hEg hgap hcomp ψ hψ).1

#print exact_unbounded_statement
#print exact_rayleigh_minimum
#print TheoremT.OperatorTheory.unit_variance_shift_identity
#print TheoremT.OperatorTheory.ground_complement_shift_estimate
#print TheoremT.OperatorTheory.unbounded_temple_directed_enclosure
#print TheoremT.Continuum.coulomb_temple_conditional
#print TheoremT.Continuum.coulombPartialOperator_domain_eq_H2
#print axioms exact_unbounded_statement
#print axioms exact_rayleigh_minimum
#print axioms TheoremT.OperatorTheory.unbounded_temple_directed_enclosure
#print axioms TheoremT.Continuum.coulomb_temple_conditional
end TheoremT.OperatorTheory.TempleAudit
