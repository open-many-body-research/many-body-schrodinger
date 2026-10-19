import SO2PolynomialSeriesDescent_v1
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Identification with a supplied Cartesian Taylor representation, and
preservation of the original bound M on the full descended polydisc.
Square roots are used only to evaluate an already analytic descended series;
no analytic square-root branch at zero is claimed or differentiated. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum
variable {d : ℕ}

theorem so2_series_function_eq_descended
    (P : ℕ → (Fin d → ℕ) → MvPolynomial (Fin 2) ℂ)
    (F : ((Fin 2 → ℂ) × (Fin d → ℂ)) → ℂ)
    (hP : ∀ n γ, (P n γ).IsHomogeneous n)
    (hb : ∀ n γ e, e ∈ (so2PolynomialToBalanced (P n γ)).support → e 0=e 1)
    {M h : ℝ} (hM : 0 ≤ M) (hh : 0 < h)
    (hc : ∀ m γ, ‖(P (2*m) γ).coeff (Finsupp.single 0 (2*m))‖ ≤
      M*(h⁻¹)^(2*m+∑ i : Fin d, γ i))
    (hF : ∀ z : (Fin 2 → ℂ) × (Fin d → ℂ),
      (∀ i, ‖z.1 i‖ < h) → ‖z.2‖ < h →
      HasSum (fun k => so2CartesianSeriesTerm P k z) (F z))
    (z : (Fin 2 → ℂ) × (Fin d → ℂ))
    (hz : ∀ i, ‖z.1 i‖ < h) (hs : ‖z.2‖ < h)
    (hw : ‖z.1 0^2+z.1 1^2‖ < h^2) :
    F z = scalarSpectatorSum (so2DescendedCoefficient P) (z.1 0^2+z.1 1^2,z.2) :=
  (hF z hz hs).unique (so2_polynomial_series_descent P hP hb hM hh hc z hw hs).2.1

theorem so2_series_descended_full_polydisc_bound
    (P : ℕ → (Fin d → ℕ) → MvPolynomial (Fin 2) ℂ)
    (F : ((Fin 2 → ℂ) × (Fin d → ℂ)) → ℂ)
    (hP : ∀ n γ, (P n γ).IsHomogeneous n)
    (hb : ∀ n γ e, e ∈ (so2PolynomialToBalanced (P n γ)).support → e 0=e 1)
    {M h : ℝ} (hM : 0 ≤ M) (hh : 0 < h)
    (hc : ∀ m γ, ‖(P (2*m) γ).coeff (Finsupp.single 0 (2*m))‖ ≤
      M*(h⁻¹)^(2*m+∑ i : Fin d, γ i))
    (hF : ∀ z : (Fin 2 → ℂ) × (Fin d → ℂ),
      (∀ i, ‖z.1 i‖ < h) → ‖z.2‖ < h →
      HasSum (fun k => so2CartesianSeriesTerm P k z) (F z))
    (hbound : ∀ z : (Fin 2 → ℂ) × (Fin d → ℂ),
      (∀ i, ‖z.1 i‖ < h) → ‖z.2‖ < h → ‖F z‖ ≤ M)
    (w : ℂ) (s : Fin d → ℂ) (hw : ‖w‖ < h^2) (hs : ‖s‖ < h) :
    ‖scalarSpectatorSum (so2DescendedCoefficient P) (w,s)‖ ≤ M := by
  obtain ⟨x,hx⟩ := IsAlgClosed.exists_pow_nat_eq w (by decide : 0 < 2)
  have hxnorm : ‖x‖^2 = ‖w‖ := by rw [← norm_pow,hx]
  have hxh : ‖x‖ < h := by nlinarith [norm_nonneg x]
  let z : (Fin 2 → ℂ) × (Fin d → ℂ) := (![x,0],s)
  have hz : ∀ i, ‖z.1 i‖ < h := by
    intro i
    fin_cases i <;> simp [z,hxh,hh]
  have hrad : z.1 0^2+z.1 1^2 = w := by simp [z,hx]
  have heq := so2_series_function_eq_descended P F hP hb hM hh hc hF z hz hs
    (by rw [hrad]; exact hw)
  have hnorm := hbound z hz hs
  rw [heq,hrad] at hnorm
  exact hnorm

end TheoremT.Continuum
