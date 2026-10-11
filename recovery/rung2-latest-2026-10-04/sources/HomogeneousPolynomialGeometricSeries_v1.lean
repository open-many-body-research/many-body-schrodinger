import HomogeneousPolynomialEvaluationBound_v1
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

/-! Absolute and uniform convergence of actual homogeneous polynomial
evaluations, derived from their literal coefficient sums and a geometric ratio.
No convergence or summability of the polynomial series is assumed. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum
variable {σ : Type*}

theorem homogeneous_polynomial_series_summable_norm
    (A : ℕ → MvPolynomial σ ℂ) (hA : ∀ n, (A n).IsHomogeneous n)
    {M D r : ℝ} (hD : 0 ≤ D) (hr : 0 ≤ r) (hDr : D*r < 1)
    (hL : ∀ n, polynomialCoeffL1 (A n) ≤ M*D^n)
    (X : σ → ℂ) (hX : X ∈ complexClosedPolydisc σ r) :
    Summable (fun n => ‖MvPolynomial.eval X (A n)‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => homogeneous_polynomial_eval_norm_geometric (A n) (hA n) hD hr (hL n) X hX)
  exact (summable_geometric_of_lt_one (mul_nonneg hD hr) hDr).mul_left M

theorem homogeneous_polynomial_series_summable
    (A : ℕ → MvPolynomial σ ℂ) (hA : ∀ n, (A n).IsHomogeneous n)
    {M D r : ℝ} (hD : 0 ≤ D) (hr : 0 ≤ r) (hDr : D*r < 1)
    (hL : ∀ n, polynomialCoeffL1 (A n) ≤ M*D^n)
    (X : σ → ℂ) (hX : X ∈ complexClosedPolydisc σ r) :
    Summable (fun n => MvPolynomial.eval X (A n)) :=
  (homogeneous_polynomial_series_summable_norm A hA hD hr hDr hL X hX).of_norm

theorem homogeneous_polynomial_series_hasSumUniformlyOn
    (A : ℕ → MvPolynomial σ ℂ) (hA : ∀ n, (A n).IsHomogeneous n)
    {M D r : ℝ} (hD : 0 ≤ D) (hr : 0 ≤ r) (hDr : D*r < 1)
    (hL : ∀ n, polynomialCoeffL1 (A n) ≤ M*D^n) :
    HasSumUniformlyOn (fun n X => MvPolynomial.eval X (A n))
      (fun X => ∑' n, MvPolynomial.eval X (A n)) (complexClosedPolydisc σ r) := by
  apply HasSumUniformlyOn.of_norm_le_summable
    ((summable_geometric_of_lt_one (mul_nonneg hD hr) hDr).mul_left M)
  intro n X hX
  exact homogeneous_polynomial_eval_norm_geometric (A n) (hA n) hD hr (hL n) X hX

theorem homogeneous_polynomial_series_tendstoUniformlyOn_range
    (A : ℕ → MvPolynomial σ ℂ) (hA : ∀ n, (A n).IsHomogeneous n)
    {M D r : ℝ} (hD : 0 ≤ D) (hr : 0 ≤ r) (hDr : D*r < 1)
    (hL : ∀ n, polynomialCoeffL1 (A n) ≤ M*D^n) :
    TendstoUniformlyOn (fun N X => ∑ n ∈ Finset.range N, MvPolynomial.eval X (A n))
      (fun X => ∑' n, MvPolynomial.eval X (A n)) Filter.atTop (complexClosedPolydisc σ r) := by
  apply tendstoUniformlyOn_tsum_nat
    ((summable_geometric_of_lt_one (mul_nonneg hD hr) hDr).mul_left M)
  intro n X hX
  exact homogeneous_polynomial_eval_norm_geometric (A n) (hA n) hD hr (hL n) X hX

theorem homogeneous_polynomial_series_norm_tsum_le
    (A : ℕ → MvPolynomial σ ℂ) (hA : ∀ n, (A n).IsHomogeneous n)
    {M D r : ℝ} (hD : 0 ≤ D) (hr : 0 ≤ r) (hDr : D*r < 1)
    (hL : ∀ n, polynomialCoeffL1 (A n) ≤ M*D^n)
    (X : σ → ℂ) (hX : X ∈ complexClosedPolydisc σ r) :
    ‖∑' n, MvPolynomial.eval X (A n)‖ ≤ M/(1-D*r) := by
  have habs := homogeneous_polynomial_series_summable_norm A hA hD hr hDr hL X hX
  have hgeom := (summable_geometric_of_lt_one (mul_nonneg hD hr) hDr).mul_left M
  calc
    _ ≤ ∑' n, ‖MvPolynomial.eval X (A n)‖ := norm_tsum_le_tsum_norm habs
    _ ≤ ∑' n, M*(D*r)^n := habs.tsum_le_tsum
      (fun n => homogeneous_polynomial_eval_norm_geometric (A n) (hA n) hD hr (hL n) X hX) hgeom
    _ = M/(1-D*r) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one (mul_nonneg hD hr) hDr, div_eq_mul_inv]

end TheoremT.Continuum
