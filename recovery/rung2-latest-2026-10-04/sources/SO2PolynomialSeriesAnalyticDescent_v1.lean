import SO2PolynomialSeriesInput_v1
import SO2SeriesFunctionIdentification_v1

/-! Concrete analytic radial descent from the transparent Cartesian series
input. The resulting function is the prescribed scalar coefficient sum.
Its bound holds on the full descended polydisc; identification with the
original function uses the intersection of the two advertised domains. -/
noncomputable section
set_option autoImplicit false
namespace TheoremT.Continuum

def SO2AnalyticDescentData
    (F : ((Fin 2 → ℂ) × (Fin 2 → ℂ)) → ℂ)
    (G : (ℂ × (Fin 2 → ℂ)) → ℂ) (M h : ℝ) : Prop :=
  AnalyticOnNhd ℂ G {z | ‖z.1‖ < h^2 ∧ ‖z.2‖ < h} ∧
  (∀ w s, ‖w‖ < h^2 → ‖s‖ < h → ‖G (w,s)‖ ≤ M) ∧
  (∀ z : (Fin 2 → ℂ) × (Fin 2 → ℂ), (∀ i, ‖z.1 i‖ < h) →
    ‖z.2‖ < h → ‖z.1 0^2+z.1 1^2‖ < h^2 →
    F z = G (z.1 0^2+z.1 1^2,z.2))

theorem so2PolynomialSeriesInput_analytic_descent
    (P : ℕ → (Fin 2 → ℕ) → MvPolynomial (Fin 2) ℂ)
    (F : ((Fin 2 → ℂ) × (Fin 2 → ℂ)) → ℂ) {M h : ℝ}
    (hdata : SO2PolynomialSeriesInput P F M h)
    (hb : ∀ n γ e, e ∈ (so2PolynomialToBalanced (P n γ)).support → e 0=e 1)
    (hM : 0≤M) (hh : 0<h) :
    SO2AnalyticDescentData F (scalarSpectatorSum (so2DescendedCoefficient P)) M h := by
  obtain ⟨hP,hc,hF,hbound⟩ := hdata
  have hc' := fun m γ => hc (2*m) γ (Finsupp.single 0 (2*m))
  exact ⟨so2_polynomial_descended_sum_analytic P hM hh hc',
    so2_series_descended_full_polydisc_bound P F hP hb hM hh hc' hF hbound,
    so2_series_function_eq_descended P F hP hb hM hh hc' hF⟩

end TheoremT.Continuum
