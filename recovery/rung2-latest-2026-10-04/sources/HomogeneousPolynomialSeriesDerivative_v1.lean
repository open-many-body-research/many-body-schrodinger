import HomogeneousPolynomialSeriesAnalytic_v1
import FormalMultilinearGeometricDerivative_v1

/-! Explicit all-order complex Frechet derivative bounds for the literal
homogeneous polynomial evaluation sum. The norm is the operator norm of
the whole derivative, so coordinate word evaluations inherit the bound. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum
variable {σ : Type*} [Fintype σ]

theorem homogeneous_polynomial_series_geometric_derivative_bound
    (A : ℕ → MvPolynomial σ ℂ) (hA : ∀ n, (A n).IsHomogeneous n)
    {M D : ℝ} (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hL : ∀ n, polynomialCoeffL1 (A n) ≤ M*D^n)
    (X : σ → ℂ) (hX : D*‖X‖ < 1) (k : ℕ) :
    ‖iteratedFDeriv ℂ k (fun z => ∑' n, MvPolynomial.eval z (A n)) X‖ ≤
      (k.factorial : ℝ)*(M*D^k/(1-D*‖X‖)^(k+1)) := by
  rw [← homogeneousPolynomialMultilinearSeries_sum A hA]
  apply formalMultilinearSeries_sum_geometric_derivative_bound _ hM hD _ X hX k
  intro n
  exact (homogeneousPolynomialMultilinearSeries_norm A hA n).trans (hL n)

theorem homogeneous_polynomial_series_half_domain_factorial_bound
    (A : ℕ → MvPolynomial σ ℂ) (hA : ∀ n, (A n).IsHomogeneous n)
    {M D : ℝ} (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hL : ∀ n, polynomialCoeffL1 (A n) ≤ M*D^n)
    (X : σ → ℂ) (hX : D*‖X‖ ≤ 1/2) (k : ℕ) :
    ‖iteratedFDeriv ℂ k (fun z => ∑' n, MvPolynomial.eval z (A n)) X‖ ≤
      (2*M)*(2*D)^k*(k.factorial : ℝ) := by
  rw [← homogeneousPolynomialMultilinearSeries_sum A hA]
  apply formalMultilinearSeries_sum_half_domain_factorial_bound _ hM hD _ X hX k
  intro n
  exact (homogeneousPolynomialMultilinearSeries_norm A hA n).trans (hL n)

theorem shifted_homogeneous_polynomial_series_half_domain_factorial_bound
    (Q : ℕ → MvPolynomial σ ℂ) (hQ : ∀ n, (Q n).IsHomogeneous n)
    {M D : ℝ} (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hL : ∀ n, polynomialCoeffL1 (Q n) ≤ M*D^(n+1))
    (X : σ → ℂ) (hX : D*‖X‖ ≤ 1/2) (k : ℕ) :
    ‖iteratedFDeriv ℂ k (fun z => ∑' n, MvPolynomial.eval z (Q n)) X‖ ≤
      (2*M*D)*(2*D)^k*(k.factorial : ℝ) := by
  have hC (n : ℕ) : polynomialCoeffL1 (Q n) ≤ (M*D)*D^n := by
    calc
      _ ≤ M*D^(n+1) := hL n
      _ = (M*D)*D^n := by rw [pow_succ]; ring
  simpa only [mul_assoc] using homogeneous_polynomial_series_half_domain_factorial_bound
    Q hQ (mul_nonneg hM hD) hD hC X hX k

end TheoremT.Continuum
