import HardyTemple_v1
import HardyCoulombSymmetry_v2

/-! Conditional specialization to the actual full-spin fermionic continuum
Coulomb operator. Its domain is the previously proved weak H² domain.
The physical eigenpair and complement separator are still hypotheses;
this file does not discharge the ground-branch obligations of Theorem T. -/
noncomputable section
open scoped InnerProductSpace LinearPMap
namespace TheoremT.Continuum

theorem coulomb_temple_conditional (N : ℕ) (Z : ℝ)
    (g ψ : (coulombPartialOperator N Z).domain)
    (hg : ‖(g : FermionicSpace N)‖ = 1) (hψ : ‖(ψ : FermionicSpace N)‖ = 1)
    (E β : ℝ)
    (hEg : coulombPartialOperator N Z g = (E : ℂ) • (g : FermionicSpace N))
    (hgap : E < β)
    (hcomp : ∀ w : (coulombPartialOperator N Z).domain,
      inner ℂ (g : FermionicSpace N) (w : FermionicSpace N) = 0 →
      β * ‖(w : FermionicSpace N)‖^2 ≤
        (inner ℂ (w : FermionicSpace N) (coulombPartialOperator N Z w)).re)
    (hμ : (inner ℂ (ψ : FermionicSpace N) (coulombPartialOperator N Z ψ)).re < β) :
    (inner ℂ (ψ : FermionicSpace N) (coulombPartialOperator N Z ψ)).re -
      ‖coulombPartialOperator N Z ψ -
        ((inner ℂ (ψ : FermionicSpace N) (coulombPartialOperator N Z ψ)).re : ℂ) •
          (ψ : FermionicSpace N)‖^2 /
        (β - (inner ℂ (ψ : FermionicSpace N) (coulombPartialOperator N Z ψ)).re) ≤ E ∧
      E ≤ (inner ℂ (ψ : FermionicSpace N) (coulombPartialOperator N Z ψ)).re := by
  exact TheoremT.OperatorTheory.unbounded_temple (coulombPartialOperator N Z)
    (fun x y => (coulombPartialOperator_symmetric N Z x y).symm)
    g hg E β hEg hgap hcomp ψ hψ hμ

#print axioms coulomb_temple_conditional
end TheoremT.Continuum
