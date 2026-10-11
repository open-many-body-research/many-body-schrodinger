import SO2SpectatorRetainedRadius_v1

/-! A transparent interface containing the actual plane polynomial degree,
coefficient budget, original Cartesian sum and original function bound.
It does not include rotational invariance or the descended conclusion. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum

def SO2PolynomialSeriesInput
    (P : ℕ → (Fin 2 → ℕ) → MvPolynomial (Fin 2) ℂ)
    (F : ((Fin 2 → ℂ) × (Fin 2 → ℂ)) → ℂ) (M h : ℝ) : Prop :=
  (∀ n γ, (P n γ).IsHomogeneous n) ∧
  (∀ n γ e, ‖(P n γ).coeff e‖ ≤ M*(h⁻¹)^(n+∑ i : Fin 2,γ i)) ∧
  (∀ z : (Fin 2 → ℂ) × (Fin 2 → ℂ), (∀ i, ‖z.1 i‖<h) → ‖z.2‖<h →
    HasSum (fun k => so2CartesianSeriesTerm P k z) (F z)) ∧
  (∀ z : (Fin 2 → ℂ) × (Fin 2 → ℂ), (∀ i, ‖z.1 i‖<h) → ‖z.2‖<h → ‖F z‖≤M)

theorem so2PolynomialSeriesInput_of_joint_polynomials
    (Q : ℕ → MvPolynomial (Fin 2 ⊕ Fin 2) ℂ)
    (F : ((Fin 2 → ℂ) × (Fin 2 → ℂ)) → ℂ)
    (hQ : ∀ n, (Q n).IsHomogeneous n) {C B M h : ℝ}
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hCM : C ≤ M) (hh : 0 < h) (hBh : B*h ≤ 1)
    (hL : ∀ n, polynomialCoeffL1 (Q n) ≤ C*B^n)
    (hF : ∀ z : (Fin 2 → ℂ) × (Fin 2 → ℂ), ‖z‖<h →
      HasSum (fun n => MvPolynomial.eval (Sum.elim z.1 z.2) (Q n)) (F z))
    (hbound : ∀ z : (Fin 2 → ℂ) × (Fin 2 → ℂ), ‖z‖<h → ‖F z‖≤M) :
    SO2PolynomialSeriesInput (so2SpectatorFamily Q) F M h := by
  refine ⟨so2SpectatorFamily_homogeneous Q hQ,
    so2SpectatorFamily_retained_coefficient_bound Q hC hB hCM hh hBh hL,
    so2SpectatorFamily_hasSum_on_retained_polydisc Q F hQ hC hB hh hBh hL hF, ?_⟩
  intro z hz hs
  apply hbound z
  have hy := (pi_norm_lt_iff hh).mpr hz
  simpa only [Prod.norm_def] using max_lt hy hs

end TheoremT.Continuum
