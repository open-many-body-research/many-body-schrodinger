import SelfAdjointRealRange_v2

/-! The ordinary bounded-inverse definition of the spectrum of an actual
partially defined operator. Its domain is retained exactly under shifts.
No eigenvalue, spectral measure, attainment or energy identification is
built into these definitions. -/
noncomputable section
open scoped InnerProductSpace ComplexConjugate LinearPMap
namespace TheoremT.OperatorTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The same-domain operator A-z. -/
def operatorShift (A : E →ₗ.[ℂ] E) (z : ℂ) : E →ₗ.[ℂ] E where
  domain := A.domain
  toFun := A.toFun - z • A.domain.subtype

theorem operatorShift_apply (A : E →ₗ.[ℂ] E) (z : ℂ) (x : A.domain) :
    operatorShift A z x = A x - z • (x : E) := rfl

/-- A bounded inverse into the exact domain, inverse on both sides. -/
def HasBoundedInverse (A : E →ₗ.[ℂ] E) : Prop :=
  ∃ R : E →L[ℂ] E, ∃ hR : ∀ y : E, R y ∈ A.domain,
    (∀ y : E, A ⟨R y, hR y⟩ = y) ∧
    (∀ x : A.domain, R (A x) = (x : E))

def unboundedResolventSet (A : E →ₗ.[ℂ] E) : Set ℂ :=
  {z | HasBoundedInverse (operatorShift A z)}

def unboundedSpectrum (A : E →ₗ.[ℂ] E) : Set ℂ :=
  (unboundedResolventSet A)ᶜ

theorem mem_unboundedSpectrum_iff (A : E →ₗ.[ℂ] E) (z : ℂ) :
    z ∈ unboundedSpectrum A ↔ ¬ HasBoundedInverse (operatorShift A z) := Iff.rfl

theorem selfAdjoint_formalAdjoint {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A) :
    A.IsFormalAdjoint A := by
  have h := A.adjoint_isFormalAdjoint hA.dense_domain
  rwa [LinearPMap.isSelfAdjoint_def.mp hA] at h

theorem formalAdjoint_real_shift {A : E →ₗ.[ℂ] E} (hA : A.IsFormalAdjoint A)
    (t : ℝ) : (operatorShift A (t : ℂ)).IsFormalAdjoint (operatorShift A (t : ℂ)) := by
  intro x y
  change inner ℂ (A x - (t : ℂ) • (x : E)) (y : E) =
    inner ℂ (x : E) (A y - (t : ℂ) • (y : E))
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal, hA x y]

theorem selfAdjoint_real_shift {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A) (t : ℝ) :
    IsSelfAdjoint (operatorShift A (t : ℂ)) := by
  let S := operatorShift A (t : ℂ)
  have hd : Dense (S.domain : Set E) := hA.dense_domain
  have hs : S.IsFormalAdjoint S := formalAdjoint_real_shift (selfAdjoint_formalAdjoint hA) t
  have hsub : S ≤ S.adjoint := hs.le_adjoint hd
  have hdom : S.adjoint.domain ≤ S.domain := by
    intro f hf
    have haf : f ∈ A.adjoint.domain := by
      apply A.mem_adjoint_domain_of_exists f
      refine ⟨S.adjoint ⟨f, hf⟩ + (t : ℂ) • f, ?_⟩
      intro x
      have hid := S.adjoint_isFormalAdjoint hd ⟨f, hf⟩ x
      change inner ℂ (S.adjoint ⟨f, hf⟩) (x : E) =
        inner ℂ f (A x - (t : ℂ) • (x : E)) at hid
      simp only [inner_add_left, inner_smul_left, Complex.conj_ofReal,
        hid, inner_sub_right, inner_smul_right]
      ring
    rwa [LinearPMap.isSelfAdjoint_def.mp hA] at haf
  rw [LinearPMap.isSelfAdjoint_def]
  apply le_antisymm _ hsub
  refine ⟨hdom, ?_⟩
  intro f u hfu
  exact (hsub.2 (x := u) (y := f) hfu.symm).symm

#print axioms operatorShift
#print axioms HasBoundedInverse
#print axioms unboundedSpectrum
#print axioms selfAdjoint_real_shift
end TheoremT.OperatorTheory
