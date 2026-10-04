import HomogeneousPolynomialGeometricSeries_v1

/-! The shifted coefficient profile for an odd radial series. Q_n has actual
degree n while its coefficient bound uses D^(n+1), so its sum has amplitude
M*D, with no additional factor of the evaluation radius. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum
variable {σ : Type*}

theorem shifted_homogeneous_polynomial_series_closed_polydisc
    (Q : ℕ → MvPolynomial σ ℂ) (hQ : ∀ n, (Q n).IsHomogeneous n)
    {M D r : ℝ} (hD : 0 ≤ D) (hr : 0 ≤ r) (hDr : D*r < 1)
    (hL : ∀ n, polynomialCoeffL1 (Q n) ≤ M*D^(n+1)) :
    (∀ X ∈ complexClosedPolydisc σ r,
      Summable (fun n => ‖MvPolynomial.eval X (Q n)‖) ∧
      Summable (fun n => MvPolynomial.eval X (Q n)) ∧
      ‖∑' n, MvPolynomial.eval X (Q n)‖ ≤ (M*D)/(1-D*r)) ∧
    HasSumUniformlyOn (fun n X => MvPolynomial.eval X (Q n))
      (fun X => ∑' n, MvPolynomial.eval X (Q n)) (complexClosedPolydisc σ r) ∧
    TendstoUniformlyOn (fun N X => ∑ n ∈ Finset.range N, MvPolynomial.eval X (Q n))
      (fun X => ∑' n, MvPolynomial.eval X (Q n)) Filter.atTop (complexClosedPolydisc σ r) := by
  have hC (n : ℕ) : polynomialCoeffL1 (Q n) ≤ (M*D)*D^n := by
    calc
      _ ≤ M*D^(n+1) := hL n
      _ = (M*D)*D^n := by rw [pow_succ]; ring
  refine ⟨?_, homogeneous_polynomial_series_hasSumUniformlyOn Q hQ hD hr hDr hC,
    homogeneous_polynomial_series_tendstoUniformlyOn_range Q hQ hD hr hDr hC⟩
  intro X hX
  exact ⟨homogeneous_polynomial_series_summable_norm Q hQ hD hr hDr hC X hX,
    homogeneous_polynomial_series_summable Q hQ hD hr hDr hC X hX,
    homogeneous_polynomial_series_norm_tsum_le Q hQ hD hr hDr hC X hX⟩

end TheoremT.Continuum
