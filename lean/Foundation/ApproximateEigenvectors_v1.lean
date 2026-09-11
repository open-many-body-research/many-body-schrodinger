import NonrealResolvent_v2
import CoerciveSelfAdjointInverse_v1

/-! Actual approximate eigenvectors for self-adjoint unbounded operators.
No eigenvector attainment, compactness, or spectral measure is assumed.
The existential vectors are not an executable selection procedure. -/
noncomputable section
open scoped LinearPMap
namespace TheoremT.OperatorTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem norm_lower_bound_of_unit_lower_bound (A : E →ₗ.[ℂ] E) (δ : ℝ)
    (hunit : ∀ x : A.domain, ‖(x : E)‖ = 1 → δ ≤ ‖A x‖) :
    ∀ x : A.domain, δ * ‖(x : E)‖ ≤ ‖A x‖ := by
  intro x
  by_cases hx : ‖(x : E)‖ = 0
  · simp only [hx, mul_zero]
    exact norm_nonneg _
  have hxpos : 0 < ‖(x : E)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx)
  let y : A.domain := ((‖(x : E)‖⁻¹ : ℝ) : ℂ) • x
  have hny : ‖(y : E)‖ = 1 := by
    change ‖((‖(x : E)‖⁻¹ : ℝ) : ℂ) • (x : E)‖ = 1
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ hx]
  have hAy : ‖A y‖ = ‖(x : E)‖⁻¹ * ‖A x‖ := by
    change ‖A.toFun (((‖(x : E)‖⁻¹ : ℝ) : ℂ) • x)‖ = _
    rw [map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    rfl
  have hb := hunit y hny
  rw [hAy] at hb
  exact (le_div_iff₀ hxpos).mp (by simpa only [div_eq_mul_inv, mul_comm] using hb)

theorem selfAdjoint_spectral_point_approximate_eigenvector (A : E →ₗ.[ℂ] E)
    (hA : IsSelfAdjoint A) (r : ℝ) (hr : (r : ℂ) ∈ unboundedSpectrum A)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ x : A.domain, ‖(x : E)‖ = 1 ∧ ‖A x - (r : ℂ) • (x : E)‖ < δ := by
  by_contra hnone
  push Not at hnone
  have hbound : ∀ x : (operatorShift A (r : ℂ)).domain,
      δ * ‖(x : E)‖ ≤ ‖operatorShift A (r : ℂ) x‖ :=
    norm_lower_bound_of_unit_lower_bound _ δ hnone
  obtain ⟨R,hR,hright,hleft,_⟩ := coercive_selfAdjoint_bounded_inverse
    (operatorShift A (r : ℂ)) (selfAdjoint_real_shift hA r) hδ hbound
  exact hr ⟨R,hR,hright,hleft⟩

#print axioms norm_lower_bound_of_unit_lower_bound
#print axioms selfAdjoint_spectral_point_approximate_eigenvector
end TheoremT.OperatorTheory
