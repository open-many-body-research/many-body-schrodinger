import SO2DescendedSeriesRadius_v1
import SO2HomogeneousRadialDescent_v1
import EvenFirstCoordinateHasSum_v1

/-! Descent of the actual entire homogeneous Cartesian polynomial family.
The scalar radial coefficient is exactly the original x^(2m)y^0 coefficient.
Odd Cartesian degrees are proved zero before the infinite sum is reindexed.
Balance of the literal inverse substitution remains an explicit premise. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum
variable {d : ℕ}

def so2DescendedCoefficient
    (P : ℕ → (Fin d → ℕ) → MvPolynomial (Fin 2) ℂ)
    (m : ℕ) (γ : Fin d → ℕ) : ℂ :=
  (P (2*m) γ).coeff (Finsupp.single 0 (2*m))

def so2CartesianSeriesTerm
    (P : ℕ → (Fin d → ℕ) → MvPolynomial (Fin 2) ℂ)
    (k : ℕ × (Fin d → ℕ)) (z : (Fin 2 → ℂ) × (Fin d → ℂ)) : ℂ :=
  MvPolynomial.eval z.1 (P k.1 k.2) * ∏ i : Fin d, z.2 i ^ k.2 i

def so2CartesianSeriesSum
    (P : ℕ → (Fin d → ℕ) → MvPolynomial (Fin 2) ℂ)
    (z : (Fin 2 → ℂ) × (Fin d → ℂ)) : ℂ :=
  ∑' k, so2CartesianSeriesTerm P k z

theorem so2CartesianSeriesTerm_even
    (P : ℕ → (Fin d → ℕ) → MvPolynomial (Fin 2) ℂ)
    (hP : ∀ n γ, (P n γ).IsHomogeneous n)
    (hb : ∀ n γ e, e ∈ (so2PolynomialToBalanced (P n γ)).support → e 0=e 1)
    (k : ℕ × (Fin d → ℕ)) (z : (Fin 2 → ℂ) × (Fin d → ℂ)) :
    so2CartesianSeriesTerm P (2*k.1,k.2) z =
      scalarSpectatorTerm (so2DescendedCoefficient P) k (z.1 0^2+z.1 1^2,z.2) := by
  unfold so2CartesianSeriesTerm
  rw [so2_homogeneous_even_radial_descent (P (2*k.1) k.2) k.1 (hP _ _) (hb _ _)]
  simp [scalarSpectatorTerm,so2DescendedCoefficient,so2RadialSquare]

theorem so2CartesianSeriesTerm_odd
    (P : ℕ → (Fin d → ℕ) → MvPolynomial (Fin 2) ℂ)
    (hP : ∀ n γ, (P n γ).IsHomogeneous n)
    (hb : ∀ n γ e, e ∈ (so2PolynomialToBalanced (P n γ)).support → e 0=e 1)
    (m : ℕ) (γ : Fin d → ℕ) (z : (Fin 2 → ℂ) × (Fin d → ℂ)) :
    so2CartesianSeriesTerm P (2*m+1,γ) z = 0 := by
  unfold so2CartesianSeriesTerm
  rw [so2_homogeneous_odd_eq_zero (P (2*m+1) γ) m (hP _ _) (hb _ _)]
  simp

theorem so2_polynomial_series_descent
    (P : ℕ → (Fin d → ℕ) → MvPolynomial (Fin 2) ℂ)
    (hP : ∀ n γ, (P n γ).IsHomogeneous n)
    (hb : ∀ n γ e, e ∈ (so2PolynomialToBalanced (P n γ)).support → e 0=e 1)
    {M h : ℝ} (hM : 0 ≤ M) (hh : 0 < h)
    (hc : ∀ m γ, ‖(P (2*m) γ).coeff (Finsupp.single 0 (2*m))‖ ≤
      M*(h⁻¹)^(2*m+∑ i : Fin d, γ i))
    (z : (Fin 2 → ℂ) × (Fin d → ℂ))
    (hw : ‖z.1 0^2+z.1 1^2‖ < h^2) (hs : ‖z.2‖ < h) :
    Summable (fun k => ‖so2CartesianSeriesTerm P k z‖) ∧
    HasSum (fun k => so2CartesianSeriesTerm P k z)
      (scalarSpectatorSum (so2DescendedCoefficient P) (z.1 0^2+z.1 1^2,z.2)) ∧
    so2CartesianSeriesSum P z =
      scalarSpectatorSum (so2DescendedCoefficient P) (z.1 0^2+z.1 1^2,z.2) := by
  have hrate := so2_descended_coefficient_rate (so2DescendedCoefficient P) hc
  have hwr : (h^2)⁻¹*‖z.1 0^2+z.1 1^2‖ < 1 :=
    (inv_mul_lt_iff₀ (sq_pos_of_pos hh)).mpr (by simpa using hw)
  have hsr : h⁻¹*‖z.2‖ < 1 := (inv_mul_lt_iff₀ hh).mpr (by simpa using hs)
  have hseries := scalar_spectator_series_closed_polydiscs (so2DescendedCoefficient P) hM
    (inv_nonneg.mpr (sq_nonneg h)) (norm_nonneg _) (inv_nonneg.mpr hh.le)
    (norm_nonneg _) hwr hsr hrate
  have hcvg := hseries.1 (z.1 0^2+z.1 1^2,z.2) ⟨le_rfl,fun i => norm_le_pi_norm z.2 i⟩
  have heven : (fun k : ℕ × (Fin d → ℕ) => so2CartesianSeriesTerm P (2*k.1,k.2) z) =
      (fun k => scalarSpectatorTerm (so2DescendedCoefficient P) k
        (z.1 0^2+z.1 1^2,z.2)) := by
    funext k
    exact so2CartesianSeriesTerm_even P hP hb k z
  have hn : HasSum (fun k => ‖so2CartesianSeriesTerm P k z‖)
      (∑' k, ‖scalarSpectatorTerm (so2DescendedCoefficient P) k
        (z.1 0^2+z.1 1^2,z.2)‖) := by
    apply (hasSum_even_first_coordinate_iff
      (fun m γ => by rw [so2CartesianSeriesTerm_odd P hP hb m γ z,norm_zero])).mp
    simpa only [so2CartesianSeriesTerm_even P hP hb] using hcvg.1.hasSum
  have hv : HasSum (fun k => so2CartesianSeriesTerm P k z)
      (scalarSpectatorSum (so2DescendedCoefficient P) (z.1 0^2+z.1 1^2,z.2)) := by
    apply (hasSum_even_first_coordinate_iff
      (fun m γ => so2CartesianSeriesTerm_odd P hP hb m γ z)).mp
    rw [heven]
    exact hcvg.2.1.hasSum
  exact ⟨hn.summable,hv,hv.tsum_eq⟩

theorem so2_polynomial_descended_sum_analytic
    (P : ℕ → (Fin d → ℕ) → MvPolynomial (Fin 2) ℂ)
    {M h : ℝ} (hM : 0 ≤ M) (hh : 0 < h)
    (hc : ∀ m γ, ‖(P (2*m) γ).coeff (Finsupp.single 0 (2*m))‖ ≤
      M*(h⁻¹)^(2*m+∑ i : Fin d, γ i)) :
    AnalyticOnNhd ℂ (scalarSpectatorSum (so2DescendedCoefficient P))
      {z : ℂ × (Fin d → ℂ) | ‖z.1‖ < h^2 ∧ ‖z.2‖ < h} :=
  so2_descended_series_analytic (so2DescendedCoefficient P) hM hh hc

end TheoremT.Continuum
