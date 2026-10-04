import GroupedHomogeneousSpectatorAnalytic_v1
import SpectatorPolynomialSeriesReindex_v1
import HomogeneousSpectatorSeriesConvergence_v1

/-! Joint complex analyticity of the original, ungrouped double-index
polynomial/spectator sum under an isotropic coefficient budget. The equality
with the grouped analytic sum follows from proved absolute summability. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum
variable {d : ℕ}

def homogeneousSpectatorSum
    (A : ℕ → (Fin d → ℕ) → MvPolynomial (Fin 3) ℂ)
    (z : Fin 3 ⊕ Fin d → ℂ) : ℂ :=
  ∑' k : ℕ × (Fin d → ℕ),
    homogeneousSpectatorTerm A k ((fun i => z (.inl i)),(fun i => z (.inr i)))

theorem homogeneous_spectator_sum_analytic_isotropic
    (A : ℕ → (Fin d → ℕ) → MvPolynomial (Fin 3) ℂ)
    (hA : ∀ m γ, (A m γ).IsHomogeneous m) {M T : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hL : ∀ m γ, polynomialCoeffL1 (A m γ) ≤ M*T^(m+∑ i : Fin d, γ i)) :
    AnalyticOnNhd ℂ (homogeneousSpectatorSum A)
      {z : Fin 3 ⊕ Fin d → ℂ | T*‖z‖ < 1} := by
  apply AnalyticOnNhd.congr (isOpen_lt (continuous_const.mul continuous_norm) continuous_const)
    (grouped_homogeneous_spectator_series_analytic A hA hM hT hL)
  intro z hz
  have hL' (m : ℕ) (γ : Fin d → ℕ) :
      polynomialCoeffL1 (A m γ) ≤ M*T^m*T^(∑ i : Fin d, γ i) := by
    simpa only [pow_add,mul_assoc] using hL m γ
  have hbound := homogeneous_spectator_series_closed_polydiscs A hA hM hT (norm_nonneg z)
    hT (norm_nonneg z) hz hz hL'
  have hmem : ((fun i => z (.inl i)),(fun i => z (.inr i))) ∈
      complexClosedPolydisc (Fin 3) ‖z‖ ×ˢ complexClosedPolydisc (Fin d) ‖z‖ :=
    ⟨fun i => norm_le_pi_norm z (.inl i),fun i => norm_le_pi_norm z (.inr i)⟩
  have hs := (hbound.1 _ hmem).2.1
  have heq := groupedHomogeneousSpectatorPolynomial_tsum_eq A
    (fun i => z (.inl i)) (fun i => z (.inr i)) hs
  have hzeta : Sum.elim (fun i => z (.inl i)) (fun i => z (.inr i)) = z := by
    funext i
    cases i <;> rfl
  simpa only [hzeta,homogeneousSpectatorSum,homogeneousSpectatorTerm] using heq

end TheoremT.Continuum
