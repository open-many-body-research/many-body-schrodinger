import PositiveInverseBound_v2
import CoerciveSelfAdjointInverse_v1

/-! Variational lower bounds identify the bottom of the actual bounded-inverse
spectrum on the real axis. No attainment or gap hypothesis is used. The
existence and value of a greatest variational lower bound remain explicit
in this generic theorem and must be established for the physical operator. -/
noncomputable section
open scoped InnerProductSpace LinearPMap
namespace TheoremT.OperatorTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
local instance : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E

def operatorLowerBounds (A : E →ₗ.[ℂ] E) : Set ℝ :=
  {a | ∀ x : A.domain, a * ‖(x : E)‖^2 ≤ inner ℝ (x : E) (A x)}

theorem inner_real_operatorShift (A : E →ₗ.[ℂ] E) (t : ℝ) (x : A.domain) :
    inner ℝ (x : E) (operatorShift A (t : ℂ) x) =
      inner ℝ (x : E) (A x) - t * ‖(x : E)‖^2 := by
  change (inner ℂ (x : E) (A x - (t : ℂ) • (x : E))).re =
    (inner ℂ (x : E) (A x)).re - t * ‖(x : E)‖^2
  rw [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]

theorem lower_bound_shift_coercive (A : E →ₗ.[ℂ] E) {m t : ℝ}
    (hm : m ∈ operatorLowerBounds A) (ht : t < m) (x : A.domain) :
    (m-t) * ‖(x : E)‖ ≤ ‖operatorShift A (t : ℂ) x‖ := by
  have he := hm x
  have hb := real_inner_le_norm (x : E) (operatorShift A (t : ℂ) x)
  rw [inner_real_operatorShift] at hb
  by_cases hx : ‖(x : E)‖ = 0
  · simp only [hx, mul_zero]
    exact norm_nonneg _
  · have hxpos : 0 < ‖(x : E)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx)
    nlinarith

theorem below_lower_bound_mem_resolvent (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A)
    {m t : ℝ} (hm : m ∈ operatorLowerBounds A) (ht : t < m) :
    (t : ℂ) ∈ unboundedResolventSet A := by
  obtain ⟨R,hR,hr,hl,_⟩ := coercive_selfAdjoint_bounded_inverse
    (operatorShift A (t : ℂ)) (selfAdjoint_real_shift hA t) (sub_pos.mpr ht)
    (lower_bound_shift_coercive A hm ht)
  exact ⟨R,hR,hr,hl⟩

theorem greatest_lower_bound_mem_spectrum (A : E →ₗ.[ℂ] E)
    (hsym : A.IsFormalAdjoint A) {m : ℝ} (hm : IsGreatest (operatorLowerBounds A) m) :
    (m : ℂ) ∈ unboundedSpectrum A := by
  rw [mem_unboundedSpectrum_iff]
  rintro ⟨R,hR,hr,_⟩
  have hpos : ∀ x : (operatorShift A (m : ℂ)).domain,
      0 ≤ inner ℝ (x : E) (operatorShift A (m : ℂ) x) := by
    intro x
    rw [inner_real_operatorShift A m x]
    exact sub_nonneg.mpr (hm.1 x)
  have himprove : m + (‖R‖+1)⁻¹ ∈ operatorLowerBounds A := by
    intro x
    have h := positive_inverse_uniform_lower_bound (operatorShift A (m : ℂ))
      (formalAdjoint_real_shift hsym m) hpos R hR hr x
    rw [inner_real_operatorShift] at h
    nlinarith
  have hle := hm.2 himprove
  have hpos : 0 < (‖R‖+1)⁻¹ := by positivity
  linarith

/-- The exact least real spectral point equals the greatest form lower bound.
This remains valid when the spectral bottom is not an eigenvalue. -/
theorem isLeast_real_spectrum_of_greatest_lower_bound (A : E →ₗ.[ℂ] E)
    (hA : IsSelfAdjoint A) {m : ℝ} (hm : IsGreatest (operatorLowerBounds A) m) :
    IsLeast {t : ℝ | (t : ℂ) ∈ unboundedSpectrum A} m := by
  refine ⟨greatest_lower_bound_mem_spectrum A (selfAdjoint_formalAdjoint hA) hm, ?_⟩
  intro t ht
  by_contra h
  exact ht (below_lower_bound_mem_resolvent A hA hm.1 (lt_of_not_ge h))

#print axioms below_lower_bound_mem_resolvent
#print axioms greatest_lower_bound_mem_spectrum
#print axioms isLeast_real_spectrum_of_greatest_lower_bound
end TheoremT.OperatorTheory
