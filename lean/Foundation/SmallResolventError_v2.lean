import SelfAdjointRealRange_v2
import Mathlib.Analysis.SpecificLimits.Normed

/-! Resolvent-error composition for an actual unbounded operator. A concrete
domain-valued candidate right inverse with a bounded error of norm <1 yields
surjectivity, then self-adjointness under the explicit symmetry hypothesis.
No Coulomb resolvent is supplied or assumed by this generic theorem.
-/
noncomputable section
open scoped InnerProductSpace LinearPMap
namespace TheoremT.OperatorTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem surjective_shift_of_small_resolvent_error (H : E →ₗ.[ℂ] E) (c : ℝ)
    (R B : E →L[ℂ] E) (hR : ∀ y : E, R y ∈ H.domain)
    (hidentity : ∀ y : E, H ⟨R y, hR y⟩ + (c : ℂ) • R y = y + B y)
    (hB : ‖B‖ < 1) :
    ∀ y : E, ∃ x : H.domain, H x + (c : ℂ) • (x : E) = y := by
  have hi : IsUnit (1 + B) := by
    simpa only [norm_neg, sub_neg_eq_add] using
      (isUnit_one_sub_of_norm_lt_one (x := -B) (by simpa only [norm_neg] using hB))
  obtain ⟨u, hu⟩ := hi
  intro y
  let z : E := (↑(u⁻¹) : E →L[ℂ] E) y
  have hz : z + B z = y := by
    change ((1 + B : E →L[ℂ] E) z) = y
    rw [← hu]
    change ((↑u : E →L[ℂ] E) * (↑(u⁻¹) : E →L[ℂ] E)) y = y
    simp
  exact ⟨⟨R z, hR z⟩, (hidentity z).trans hz⟩

theorem selfAdjoint_of_small_resolvent_error (H : E →ₗ.[ℂ] E) (c : ℝ)
    (hdense : Dense (H.domain : Set E)) (hsym : H.IsFormalAdjoint H)
    (R B : E →L[ℂ] E) (hR : ∀ y : E, R y ∈ H.domain)
    (hidentity : ∀ y : E, H ⟨R y, hR y⟩ + (c : ℂ) • R y = y + B y)
    (hB : ‖B‖ < 1) : IsSelfAdjoint H :=
  selfAdjoint_of_surjective_real_shift H c hdense hsym
    (surjective_shift_of_small_resolvent_error H c R B hR hidentity hB)

#print axioms surjective_shift_of_small_resolvent_error
#print axioms selfAdjoint_of_small_resolvent_error
end TheoremT.OperatorTheory
