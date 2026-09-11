import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Tactic

/-! A general range criterion for genuine densely defined unbounded operators.
The range hypotheses are explicit; this file does not assert that they hold for
the Coulomb Hamiltonian. The conclusion uses mathlib's actual adjoint.
-/
noncomputable section
open scoped InnerProductSpace ComplexConjugate LinearPMap
namespace TheoremT.OperatorTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A densely defined symmetric operator is self-adjoint if both shifts by i
are onto. No spectral theorem, closedness or pre-existing self-adjointness is
assumed. -/
theorem selfAdjoint_of_surjective_shifts (A : E →ₗ.[ℂ] E)
    (hdense : Dense (A.domain : Set E)) (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ y : E, ∃ x : A.domain, A x + Complex.I • (x : E) = y)
    (hminus : ∀ y : E, ∃ x : A.domain, A x - Complex.I • (x : E) = y) :
    IsSelfAdjoint A := by
  have hsub : A ≤ A.adjoint := hsym.le_adjoint hdense
  have hadj : A.IsFormalAdjoint A.adjoint := (A.adjoint_isFormalAdjoint hdense).symm
  have hpair (f : A.adjoint.domain) :
      ∃ u : A.domain, (f : E) = (u : E) ∧ A.adjoint f = A u := by
    obtain ⟨u, hu⟩ := hplus (A.adjoint f + Complex.I • (f : E))
    obtain ⟨z, hz⟩ := hminus ((f : E) - (u : E))
    have hid : inner ℂ (A z - Complex.I • (z : E)) ((f : E) - (u : E)) =
        inner ℂ (z : E) ((A.adjoint f + Complex.I • (f : E)) -
          (A u + Complex.I • (u : E))) := by
      simp only [inner_sub_left, inner_sub_right, inner_add_right,
        inner_smul_left, inner_smul_right, hadj z f, hsym z u,
        Complex.conj_I]
      ring
    rw [hz, ← hu, sub_self, inner_zero_right] at hid
    have hf : (f : E) = (u : E) := sub_eq_zero.mp ((inner_self_eq_zero).mp hid)
    refine ⟨u, hf, ?_⟩
    rw [hf] at hu
    exact (add_right_cancel hu).symm
  rw [LinearPMap.isSelfAdjoint_def]
  apply le_antisymm _ hsub
  constructor
  · intro f hf
    obtain ⟨u, hu, _⟩ := hpair ⟨f, hf⟩
    change f = (u : E) at hu
    rw [hu]
    exact u.property
  · intro f u hfu
    obtain ⟨v, hfv, hv⟩ := hpair f
    rw [hv]
    congr 1
    apply Subtype.ext
    exact hfv.symm.trans hfu

#print axioms selfAdjoint_of_surjective_shifts
end TheoremT.OperatorTheory
