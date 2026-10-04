import HomogeneousPolynomialMultilinear_v1
import HomogeneousPolynomialEvaluationBound_v1
import FormalMultilinearGeometricAnalytic_v1

/-! Complex analyticity of the literal sum of homogeneous polynomial evaluations.
The multilinear coefficients are obtained from the proved monomial representation;
their norm bounds are derived from the actual coefficient L1 sum. These are
conditional polynomial-series results, not an identification with a physical KS
pullback. The representation uses classical selection, not an executable solver. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators NNReal ENNReal
namespace TheoremT.Continuum
variable {σ : Type*} [Fintype σ]

def homogeneousPolynomialMultilinearSeries
    (A : ℕ → MvPolynomial σ ℂ) (hA : ∀ n, (A n).IsHomogeneous n) :
    FormalMultilinearSeries ℂ (σ → ℂ) ℂ :=
  fun n => (homogeneous_polynomial_multilinear_exists (A n) (hA n)).choose

theorem homogeneousPolynomialMultilinearSeries_diagonal
    (A : ℕ → MvPolynomial σ ℂ) (hA : ∀ n, (A n).IsHomogeneous n)
    (n : ℕ) (X : σ → ℂ) :
    homogeneousPolynomialMultilinearSeries A hA n (fun _ => X) = MvPolynomial.eval X (A n) :=
  (homogeneous_polynomial_multilinear_exists (A n) (hA n)).choose_spec.1 X

theorem homogeneousPolynomialMultilinearSeries_norm
    (A : ℕ → MvPolynomial σ ℂ) (hA : ∀ n, (A n).IsHomogeneous n) (n : ℕ) :
    ‖homogeneousPolynomialMultilinearSeries A hA n‖ ≤ polynomialCoeffL1 (A n) :=
  (homogeneous_polynomial_multilinear_exists (A n) (hA n)).choose_spec.2

theorem homogeneousPolynomialMultilinearSeries_sum
    (A : ℕ → MvPolynomial σ ℂ) (hA : ∀ n, (A n).IsHomogeneous n) :
    (homogeneousPolynomialMultilinearSeries A hA).sum =
      (fun X => ∑' n, MvPolynomial.eval X (A n)) := by
  funext X
  simp only [FormalMultilinearSeries.sum, homogeneousPolynomialMultilinearSeries_diagonal]

theorem homogeneous_polynomial_series_analyticOnNhd
    (A : ℕ → MvPolynomial σ ℂ) (hA : ∀ n, (A n).IsHomogeneous n)
    {M D : ℝ} (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hL : ∀ n, polynomialCoeffL1 (A n) ≤ M*D^n) :
    AnalyticOnNhd ℂ (fun X => ∑' n, MvPolynomial.eval X (A n))
      {X : σ → ℂ | D*‖X‖ < 1} := by
  rw [← homogeneousPolynomialMultilinearSeries_sum A hA]
  apply formalMultilinearSeries_analyticOnNhd_geometric _ hM hD
  intro n
  exact (homogeneousPolynomialMultilinearSeries_norm A hA n).trans (hL n)

theorem homogeneous_polynomial_series_analyticOnNhd_closed_polydisc
    (A : ℕ → MvPolynomial σ ℂ) (hA : ∀ n, (A n).IsHomogeneous n)
    {M D r : ℝ} (hM : 0 ≤ M) (hD : 0 ≤ D) (hr : 0 ≤ r) (hDr : D*r < 1)
    (hL : ∀ n, polynomialCoeffL1 (A n) ≤ M*D^n) :
    AnalyticOnNhd ℂ (fun X => ∑' n, MvPolynomial.eval X (A n))
      (complexClosedPolydisc σ r) := by
  intro X hX
  apply homogeneous_polynomial_series_analyticOnNhd A hA hM hD hL X
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left
    ((pi_norm_le_iff_of_nonneg hr).mpr hX) hD) hDr

theorem shifted_homogeneous_polynomial_series_analyticOnNhd
    (Q : ℕ → MvPolynomial σ ℂ) (hQ : ∀ n, (Q n).IsHomogeneous n)
    {M D : ℝ} (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hL : ∀ n, polynomialCoeffL1 (Q n) ≤ M*D^(n+1)) :
    AnalyticOnNhd ℂ (fun X => ∑' n, MvPolynomial.eval X (Q n))
      {X : σ → ℂ | D*‖X‖ < 1} := by
  apply homogeneous_polynomial_series_analyticOnNhd Q hQ (mul_nonneg hM hD) hD
  intro n
  calc
    _ ≤ M*D^(n+1) := hL n
    _ = (M*D)*D^n := by rw [pow_succ]; ring

end TheoremT.Continuum
