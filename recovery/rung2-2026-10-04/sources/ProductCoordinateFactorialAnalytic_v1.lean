import ProductCoordinateFrechetBound_v1
import FactorialFrechetAnalytic_v1

/-! Actual seven-coordinate word bounds imply real analyticity with the
explicit coordinate-to-operator loss 7. Smoothness is an explicit input;
no weak representative theorem or physical PDE estimate is assumed proved. -/
set_option autoImplicit false
noncomputable section
open scoped ContDiff NNReal ENNReal
namespace TheoremT.Continuum.WeakGrushin

theorem physical_coordinate_factorial_common_radius
    {Ω K : Set (Space (Fin 3))} (hΩ : IsOpen Ω) {f : Space (Fin 3) → ℂ}
    (hf : ContDiffOn ℝ ∞ f Ω) {C A δ : ℝ}
    (hC : 0 ≤ C) (hA : 0 < A) (hδ : 0 < δ)
    (hword : ∀ x ∈ Ω, ∀ w : List (Fin 4 ⊕ Fin 3),
      ‖complexDirectionalWordDeriv productCoordinateDirection f w x‖ ≤
        C*A^w.length*(w.length.factorial : ℝ))
    (hroom : ∀ x ∈ K, Metric.ball x δ ⊆ Ω) :
    ∃ r : ℝ≥0, 0 < r ∧ (r : ℝ) = min δ (7*A)⁻¹ ∧
      ∀ x ∈ K, HasFPowerSeriesOnBall f (factorialFrechetSeries f x) x (r : ℝ≥0∞) := by
  have hb : ∀ x ∈ Ω, ∀ k, ‖iteratedFDeriv ℝ k f x‖ ≤ C*(7*A)^k*(k.factorial : ℝ) := by
    have h := product_iteratedFDeriv_factorial_bound_of_coordinate_words hΩ hf hC hA.le hword
    norm_num at h
    exact fun x hx k => h x.1 x.2 hx k
  exact factorial_frechet_common_radius f hΩ hf hC (by positivity) hδ hb hroom

theorem physical_coordinate_factorial_analyticOnNhd
    {Ω : Set (Space (Fin 3))} (hΩ : IsOpen Ω) {f : Space (Fin 3) → ℂ}
    (hf : ContDiffOn ℝ ∞ f Ω) {C A : ℝ} (hC : 0 ≤ C) (hA : 0 < A)
    (hword : ∀ x ∈ Ω, ∀ w : List (Fin 4 ⊕ Fin 3),
      ‖complexDirectionalWordDeriv productCoordinateDirection f w x‖ ≤
        C*A^w.length*(w.length.factorial : ℝ)) :
    AnalyticOnNhd ℝ f Ω := by
  apply factorial_frechet_analyticOnNhd f hΩ hf hC (A := 7*A) (by positivity)
  have h := product_iteratedFDeriv_factorial_bound_of_coordinate_words hΩ hf hC hA.le hword
  norm_num at h
  exact fun x hx k => h x.1 x.2 hx k

end TheoremT.Continuum.WeakGrushin
