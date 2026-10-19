import GroupedHomogeneousSpectatorPolynomial_v1
import HomogeneousPolynomialSeriesAnalytic_v1
import FormalMultilinearBinomialGeometricAnalytic_v1

/-! The actual series grouped by total degree is jointly complex analytic
under an isotropic geometric coefficient budget. Its exact binomial block
count does not reduce the radius. Anisotropic rescaling and equality with
the original product-index sum are separate composition steps. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum
variable {σ : Type*} [Fintype σ] {d : ℕ}

theorem grouped_homogeneous_spectator_series_analytic
    (A : ℕ → (Fin d → ℕ) → MvPolynomial σ ℂ)
    (hA : ∀ m γ, (A m γ).IsHomogeneous m) {M T : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hL : ∀ m γ, polynomialCoeffL1 (A m γ) ≤ M*T^(m+∑ i : Fin d, γ i)) :
    AnalyticOnNhd ℂ
      (fun z => ∑' n, MvPolynomial.eval z (groupedHomogeneousSpectatorPolynomial A n))
      {z : σ ⊕ Fin d → ℂ | T*‖z‖ < 1} := by
  let G := groupedHomogeneousSpectatorPolynomial A
  have hG : ∀ n, (G n).IsHomogeneous n := groupedHomogeneousSpectatorPolynomial_isHomogeneous A hA
  rw [← homogeneousPolynomialMultilinearSeries_sum G hG]
  apply formalMultilinearSeries_analyticOnNhd_binomial_geometric _ d hM hT
  intro n
  exact (homogeneousPolynomialMultilinearSeries_norm G hG n).trans
    (polynomialCoeffL1_groupedHomogeneousSpectatorPolynomial A hL n)

end TheoremT.Continuum
