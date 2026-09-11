import SelfAdjointRangeCriterion_v2

noncomputable section
open scoped InnerProductSpace ComplexConjugate LinearPMap
namespace TheoremT.OperatorTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A single real shift with full range suffices for self-adjointness of an
actual densely defined symmetric operator. This is useful with a positive
free resolvent; surjectivity for the physical operator is still to be proved. -/
theorem selfAdjoint_of_surjective_real_shift (A : E →ₗ.[ℂ] E) (c : ℝ)
    (hdense : Dense (A.domain : Set E)) (hsym : A.IsFormalAdjoint A)
    (hsurj : ∀ y : E, ∃ x : A.domain, A x + (c : ℂ) • (x : E) = y) :
    IsSelfAdjoint A := by
  have hsub : A ≤ A.adjoint := hsym.le_adjoint hdense
  have hadj : A.IsFormalAdjoint A.adjoint := (A.adjoint_isFormalAdjoint hdense).symm
  have hpair (f : A.adjoint.domain) :
      ∃ u : A.domain, (f : E) = (u : E) ∧ A.adjoint f = A u := by
    obtain ⟨u, hu⟩ := hsurj (A.adjoint f + (c : ℂ) • (f : E))
    obtain ⟨z, hz⟩ := hsurj ((f : E) - (u : E))
    have hid : inner ℂ (A z + (c : ℂ) • (z : E)) ((f : E) - (u : E)) =
        inner ℂ (z : E) ((A.adjoint f + (c : ℂ) • (f : E)) -
          (A u + (c : ℂ) • (u : E))) := by
      simp only [inner_add_left, inner_sub_right, inner_add_right,
        inner_smul_left, inner_smul_right, hadj z f, hsym z u,
        Complex.conj_ofReal]
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

#print axioms selfAdjoint_of_surjective_real_shift
end TheoremT.OperatorTheory
