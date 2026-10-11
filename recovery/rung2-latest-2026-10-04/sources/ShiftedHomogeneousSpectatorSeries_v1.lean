import HomogeneousSpectatorSeriesConvergence_v1

/-! Shifted degree profile for actual double-index odd coefficient series.
Q_n_gamma has degree n, and the additional D stays in the amplitude. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum

theorem shifted_homogeneous_spectator_series_closed_polydiscs {d : ℕ}
    (Q : ℕ → (Fin d → ℕ) → MvPolynomial (Fin 3) ℂ)
    (hQ : ∀ n γ, (Q n γ).IsHomogeneous n)
    {M D r S h : ℝ} (hM : 0 ≤ M) (hD : 0 ≤ D) (hr : 0 ≤ r)
    (hS : 0 ≤ S) (hh : 0 ≤ h) (hDr : D*r < 1) (hSh : S*h < 1)
    (hL : ∀ n γ, polynomialCoeffL1 (Q n γ) ≤ M*D^(n+1)*S^(∑ i : Fin d, γ i)) :
    (∀ z ∈ complexClosedPolydisc (Fin 3) r ×ˢ complexClosedPolydisc (Fin d) h,
      Summable (fun k : ℕ × (Fin d → ℕ) => ‖homogeneousSpectatorTerm Q k z‖) ∧
      Summable (fun k : ℕ × (Fin d → ℕ) => homogeneousSpectatorTerm Q k z) ∧
      ‖∑' k : ℕ × (Fin d → ℕ), homogeneousSpectatorTerm Q k z‖ ≤
        (M*D)/((1-D*r)*(1-S*h)^d)) ∧
    HasSumUniformlyOn (homogeneousSpectatorTerm Q)
      (fun z => ∑' k : ℕ × (Fin d → ℕ), homogeneousSpectatorTerm Q k z)
      (complexClosedPolydisc (Fin 3) r ×ˢ complexClosedPolydisc (Fin d) h) := by
  have hC (n : ℕ) (γ : Fin d → ℕ) :
      polynomialCoeffL1 (Q n γ) ≤ (M*D)*D^n*S^(∑ i : Fin d, γ i) := by
    calc
      _ ≤ M*D^(n+1)*S^(∑ i : Fin d, γ i) := hL n γ
      _ = (M*D)*D^n*S^(∑ i : Fin d, γ i) := by rw [pow_succ]; ring
  exact homogeneous_spectator_series_closed_polydiscs Q hQ (mul_nonneg hM hD) hD hr hS hh hDr hSh hC

end TheoremT.Continuum
