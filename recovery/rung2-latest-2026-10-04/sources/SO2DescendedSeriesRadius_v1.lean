import ScalarSpectatorGeometricSeries_v1

/-! The exact h² by h radii of the invariant-distance scalar series.
The coefficients are supplied literally; their extraction from an invariant
Cartesian function is a separate algebraic/Taylor obligation. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum

theorem so2_descended_coefficient_rate {d : ℕ}
    (c : ℕ → (Fin d → ℕ) → ℂ) {M h : ℝ}
    (hc : ∀ m γ, ‖c m γ‖ ≤ M*(h⁻¹)^(2*m+∑ i : Fin d, γ i)) :
    ∀ m γ, ‖c m γ‖ ≤ M*((h^2)⁻¹)^m*(h⁻¹)^(∑ i : Fin d, γ i) := by
  intro m γ
  simpa only [inv_pow, ← pow_mul, pow_add, mul_assoc] using hc m γ

theorem so2_descended_series_analytic {d : ℕ}
    (c : ℕ → (Fin d → ℕ) → ℂ) {M h : ℝ} (hM : 0 ≤ M) (hh : 0 < h)
    (hc : ∀ m γ, ‖c m γ‖ ≤ M*(h⁻¹)^(2*m+∑ i : Fin d, γ i)) :
    AnalyticOnNhd ℂ (scalarSpectatorSum c)
      {z : ℂ × (Fin d → ℂ) | ‖z.1‖ < h^2 ∧ ‖z.2‖ < h} := by
  have ha := scalar_spectator_sum_analytic c hM (inv_nonneg.mpr (sq_nonneg h))
    (inv_nonneg.mpr hh.le) (so2_descended_coefficient_rate c hc)
  intro z hz
  apply ha
  constructor
  · exact (inv_mul_lt_iff₀ (sq_pos_of_pos hh)).mpr (by simpa using hz.1)
  · exact (inv_mul_lt_iff₀ hh).mpr (by simpa using hz.2)

theorem so2_descended_series_half_polyradii
    (c : ℕ → (Fin 2 → ℕ) → ℂ) {M h : ℝ} (hM : 0 ≤ M) (hh : 0 < h)
    (hc : ∀ m γ, ‖c m γ‖ ≤ M*(h⁻¹)^(2*m+∑ i : Fin 2, γ i)) :
    (∀ z ∈ {z : ℂ × (Fin 2 → ℂ) |
        ‖z.1‖ ≤ h^2/2 ∧ ∀ i, ‖z.2 i‖ ≤ h/2},
      Summable (fun k => ‖scalarSpectatorTerm c k z‖) ∧
      Summable (fun k => scalarSpectatorTerm c k z) ∧
      ‖scalarSpectatorSum c z‖ ≤ 8*M) ∧
    HasSumUniformlyOn (scalarSpectatorTerm c) (scalarSpectatorSum c)
      {z : ℂ × (Fin 2 → ℂ) | ‖z.1‖ ≤ h^2/2 ∧ ∀ i, ‖z.2 i‖ ≤ h/2} := by
  have hrad : (h^2)⁻¹*(h^2/2) = (1:ℝ)/2 := by field_simp [ne_of_gt hh]
  have hspec : h⁻¹*(h/2) = (1:ℝ)/2 := by field_simp [ne_of_gt hh]
  have ha := scalar_spectator_series_closed_polydiscs c hM
    (inv_nonneg.mpr (sq_nonneg h)) (by positivity : 0 ≤ h^2/2)
    (inv_nonneg.mpr hh.le) (by positivity : 0 ≤ h/2)
    (by rw [hrad]; norm_num) (by rw [hspec]; norm_num)
    (so2_descended_coefficient_rate c hc)
  have hden : M/((1-(h^2)⁻¹*(h^2/2))*(1-h⁻¹*(h/2))^2) = 8*M := by
    rw [hrad, hspec]
    ring
  simpa only [hden] using ha

end TheoremT.Continuum
