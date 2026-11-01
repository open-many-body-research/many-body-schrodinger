import SO2SpectatorFamilySeries_v1
import SO2PolynomialSeriesDescent_v1

/-! Explicit retained radii and amplitudes for actual extracted plane
polynomials. These lemmas derive the SO(2) coefficient and Cartesian
HasSum inputs from literal joint polynomial data. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum

theorem so2SpectatorFamily_retained_coefficient_bound
    (Q : ℕ → MvPolynomial (Fin 2 ⊕ Fin 2) ℂ) {C B M h : ℝ}
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hCM : C ≤ M) (hh : 0 < h) (hBh : B*h ≤ 1)
    (hL : ∀ n, polynomialCoeffL1 (Q n) ≤ C*B^n)
    (j : ℕ) (γ : Fin 2 → ℕ) (e : Fin 2 →₀ ℕ) :
    ‖(so2SpectatorFamily Q j γ).coeff e‖ ≤ M*(h⁻¹)^(j+∑ i : Fin 2,γ i) := by
  have hBinv : B ≤ h⁻¹ := by
    rw [inv_eq_one_div]
    exact (le_div_iff₀ hh).mpr hBh
  calc
    _ ≤ polynomialCoeffL1 (so2SpectatorFamily Q j γ) := polynomialCoeffL1_coefficient_bound _ _
    _ ≤ C*B^j*B^(∑ i : Fin 2,γ i) := so2SpectatorFamily_coefficientL1 Q hL j γ
    _ = C*B^(j+∑ i : Fin 2,γ i) := by rw [pow_add,mul_assoc]
    _ ≤ _ := mul_le_mul hCM (pow_le_pow_left₀ hB hBinv _)
      (pow_nonneg hB _) (hC.trans hCM)

theorem geometric_rate_lt_one_of_lt_retained_radius {B h r : ℝ}
    (hB : 0 ≤ B) (hh : 0 < h) (hBh : B*h ≤ 1) (hr : 0 ≤ r) (hrh : r < h) : B*r < 1 := by
  have hBinv : B ≤ h⁻¹ := by
    rw [inv_eq_one_div]
    exact (le_div_iff₀ hh).mpr hBh
  calc
    _ ≤ h⁻¹*r := mul_le_mul_of_nonneg_right hBinv hr
    _ < 1 := (inv_mul_lt_iff₀ hh).mpr (by simpa using hrh)

theorem so2SpectatorFamily_hasSum_on_retained_polydisc
    (Q : ℕ → MvPolynomial (Fin 2 ⊕ Fin 2) ℂ)
    (F : ((Fin 2 → ℂ) × (Fin 2 → ℂ)) → ℂ)
    (hQ : ∀ n, (Q n).IsHomogeneous n) {C B h : ℝ}
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hh : 0 < h) (hBh : B*h ≤ 1)
    (hL : ∀ n, polynomialCoeffL1 (Q n) ≤ C*B^n)
    (hF : ∀ z : (Fin 2 → ℂ) × (Fin 2 → ℂ), ‖z‖<h →
      HasSum (fun n => MvPolynomial.eval (Sum.elim z.1 z.2) (Q n)) (F z))
    (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) (hz : ∀ i, ‖z.1 i‖<h) (hs : ‖z.2‖<h) :
    HasSum (fun k => so2CartesianSeriesTerm (so2SpectatorFamily Q) k z) (F z) := by
  have hy : ‖z.1‖<h := (pi_norm_lt_iff hh).mpr hz
  have hprod : ‖z‖<h := by simpa only [Prod.norm_def] using max_lt hy hs
  exact so2SpectatorFamily_hasSum_of_joint_hasSum Q hQ hC hB hL z.1 z.2
    (geometric_rate_lt_one_of_lt_retained_radius hB hh hBh (norm_nonneg _) hy)
    (geometric_rate_lt_one_of_lt_retained_radius hB hh hBh (norm_nonneg _) hs)
    (hF z hprod)

end TheoremT.Continuum
