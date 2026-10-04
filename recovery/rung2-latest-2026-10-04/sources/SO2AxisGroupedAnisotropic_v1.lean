import SO2AxisGroupedSeries_v1

/-! A stated isotropic retained rate for the actual axis polynomial series,
obtained from separate radial and spectator coefficient rates. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum

theorem homogeneous_spectator_coefficient_max_rate
    (A : ℕ → (Fin 3 → ℕ) → MvPolynomial (Fin 3) ℂ) {M D S : ℝ}
    (hM : 0 ≤ M) (hD : 0 ≤ D) (hS : 0 ≤ S)
    (hL : ∀ m γ, polynomialCoeffL1 (A m γ) ≤ M*D^m*S^(∑ i : Fin 3, γ i))
    (m : ℕ) (γ : Fin 3 → ℕ) :
    polynomialCoeffL1 (A m γ) ≤ M*(max D S)^(m+∑ i : Fin 3, γ i) := by
  rw [pow_add,← mul_assoc]
  apply (hL m γ).trans
  gcongr
  · exact le_max_left D S
  · exact le_max_right D S

theorem so2AxisGroupedPolynomial_coeffL1_anisotropic
    (A : ℕ → (Fin 3 → ℕ) → MvPolynomial (Fin 3) ℂ) {M D S : ℝ}
    (hM : 0 ≤ M) (hD : 0 ≤ D) (hS : 0 ≤ S)
    (hL : ∀ m γ, polynomialCoeffL1 (A m γ) ≤ M*D^m*S^(∑ i : Fin 3, γ i)) (n : ℕ) :
    polynomialCoeffL1 (so2AxisGroupedPolynomial A n) ≤ (8*M)*(2*max D S)^n :=
  so2AxisGroupedPolynomial_coeffL1 A hM (hD.trans (le_max_left _ _))
    (homogeneous_spectator_coefficient_max_rate A hM hD hS hL) n

theorem so2AxisGroupedPolynomial_hasSum_anisotropic
    (A : ℕ → (Fin 3 → ℕ) → MvPolynomial (Fin 3) ℂ)
    (hA : ∀ m γ, (A m γ).IsHomogeneous m) {M D S : ℝ}
    (hM : 0 ≤ M) (hD : 0 ≤ D) (hS : 0 ≤ S)
    (hL : ∀ m γ, polynomialCoeffL1 (A m γ) ≤ M*D^m*S^(∑ i : Fin 3, γ i))
    (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) (hz : (2*max D S)*‖z‖ < 1) :
    Summable (fun n => ‖MvPolynomial.eval (Sum.elim z.1 z.2) (so2AxisGroupedPolynomial A n)‖) ∧
    HasSum (fun n => MvPolynomial.eval (Sum.elim z.1 z.2) (so2AxisGroupedPolynomial A n))
      (homogeneousSpectatorSum A (Sum.elim ![z.1 0,z.1 1,z.2 0] ![0,0,z.2 1])) :=
  so2AxisGroupedPolynomial_hasSum A hA hM (hD.trans (le_max_left _ _))
    (homogeneous_spectator_coefficient_max_rate A hM hD hS hL) z hz

end TheoremT.Continuum
