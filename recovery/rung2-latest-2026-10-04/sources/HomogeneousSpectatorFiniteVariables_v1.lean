import HomogeneousSpectatorSeriesMajorant_v1

/-! Absolute convergence with an arbitrary finite polynomial coordinate block.
This includes the four KS variables before radial descent. The terms are the
literal evaluations of the prescribed homogeneous polynomial coefficients. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum
variable {σ : Type*} {d : ℕ}

theorem homogeneous_spectator_finite_variables_norm_bound
    (A : ℕ → (Fin d → ℕ) → MvPolynomial σ ℂ)
    (hA : ∀ m γ, (A m γ).IsHomogeneous m)
    {M D r S h : ℝ} (hr : 0 ≤ r) (hh : 0 ≤ h)
    (hL : ∀ m γ, polynomialCoeffL1 (A m γ) ≤ M*D^m*S^(∑ i : Fin d, γ i))
    (y : σ → ℂ) (t : Fin d → ℂ)
    (hy : y ∈ complexClosedPolydisc σ r) (ht : t ∈ complexClosedPolydisc (Fin d) h)
    (k : ℕ × (Fin d → ℕ)) :
    ‖MvPolynomial.eval y (A k.1 k.2) * ∏ i : Fin d, t i ^ k.2 i‖ ≤
      homogeneousSpectatorMajorant M D r S h k := by
  have he := homogeneous_polynomial_eval_norm_bound (A k.1 k.2) (hA k.1 k.2) y hr hy
  have hm := spectator_monomial_norm_bound t k.2 hh ht
  rw [norm_mul]
  calc
    _ ≤ (polynomialCoeffL1 (A k.1 k.2)*r^k.1)*h^(∑ i : Fin d, k.2 i) :=
      mul_le_mul he hm (norm_nonneg _)
        (mul_nonneg (polynomialCoeffL1_nonneg _) (pow_nonneg hr _))
    _ ≤ ((M*D^k.1*S^(∑ i : Fin d, k.2 i))*r^k.1)*h^(∑ i : Fin d, k.2 i) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hL k.1 k.2) (pow_nonneg hr _)) (pow_nonneg hh _)
    _ = homogeneousSpectatorMajorant M D r S h k := by
      unfold homogeneousSpectatorMajorant spectatorGeometricWeight
      rw [Finset.prod_pow_eq_pow_sum, mul_pow, mul_pow]
      ring

theorem homogeneous_spectator_finite_variables_summable
    (A : ℕ → (Fin d → ℕ) → MvPolynomial σ ℂ)
    (hA : ∀ m γ, (A m γ).IsHomogeneous m)
    {M D r S h : ℝ} (hM : 0 ≤ M) (hD : 0 ≤ D) (hr : 0 ≤ r)
    (hS : 0 ≤ S) (hh : 0 ≤ h) (hDr : D*r < 1) (hSh : S*h < 1)
    (hL : ∀ m γ, polynomialCoeffL1 (A m γ) ≤ M*D^m*S^(∑ i : Fin d, γ i))
    (y : σ → ℂ) (t : Fin d → ℂ)
    (hy : y ∈ complexClosedPolydisc σ r) (ht : t ∈ complexClosedPolydisc (Fin d) h) :
    Summable (fun k : ℕ × (Fin d → ℕ) =>
      ‖MvPolynomial.eval y (A k.1 k.2) * ∏ i : Fin d, t i ^ k.2 i‖) ∧
    Summable (fun k : ℕ × (Fin d → ℕ) =>
      MvPolynomial.eval y (A k.1 k.2) * ∏ i : Fin d, t i ^ k.2 i) := by
  have hu := homogeneous_spectator_majorant_summable (d := d) hM hD hr hS hh hDr hSh
  have habs : Summable (fun k : ℕ × (Fin d → ℕ) =>
      ‖MvPolynomial.eval y (A k.1 k.2) * ∏ i : Fin d, t i ^ k.2 i‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (homogeneous_spectator_finite_variables_norm_bound A hA hr hh hL y t hy ht) hu
  exact ⟨habs, habs.of_norm⟩

end TheoremT.Continuum
