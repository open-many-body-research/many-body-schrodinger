import ShiftedHomogeneousPolynomialGeometricSeries_v1

/-! Restore the original odd-series index. The zero first polynomial is an
explicit hypothesis, so removing it is justified by actual summability and
the sum decomposition theorem. Uniform convergence includes every original
range partial sum, including the empty sum. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum
variable {σ : Type*}

theorem odd_homogeneous_polynomial_series_zero_first
    (B : ℕ → MvPolynomial σ ℂ) (hB0 : B 0 = 0)
    (hB : ∀ n, (B (n+1)).IsHomogeneous n)
    {M D r : ℝ} (hD : 0 ≤ D) (hr : 0 ≤ r) (hDr : D*r < 1)
    (hL : ∀ n, polynomialCoeffL1 (B (n+1)) ≤ M*D^(n+1)) :
    (∀ X ∈ complexClosedPolydisc σ r,
      Summable (fun m => ‖MvPolynomial.eval X (B m)‖) ∧
      Summable (fun m => MvPolynomial.eval X (B m)) ∧
      (∑' m, MvPolynomial.eval X (B m)) = (∑' n, MvPolynomial.eval X (B (n+1))) ∧
      ‖∑' m, MvPolynomial.eval X (B m)‖ ≤ (M*D)/(1-D*r)) ∧
    HasSumUniformlyOn (fun m X => MvPolynomial.eval X (B m))
      (fun X => ∑' m, MvPolynomial.eval X (B m)) (complexClosedPolydisc σ r) ∧
    TendstoUniformlyOn (fun N X => ∑ m ∈ Finset.range N, MvPolynomial.eval X (B m))
      (fun X => ∑' m, MvPolynomial.eval X (B m)) Filter.atTop (complexClosedPolydisc σ r) := by
  let u : ℕ → ℝ := fun m => if m=0 then 0 else (M*D)*(D*r)^(m-1)
  have hu : Summable u := by
    apply (summable_nat_add_iff 1).mp
    simpa [u] using (summable_geometric_of_lt_one (mul_nonneg hD hr) hDr).mul_left (M*D)
  have hC (n : ℕ) : polynomialCoeffL1 (B (n+1)) ≤ (M*D)*D^n := by
    calc
      _ ≤ M*D^(n+1) := hL n
      _ = (M*D)*D^n := by rw [pow_succ]; ring
  have hbound (m : ℕ) (X : σ → ℂ) (hX : X ∈ complexClosedPolydisc σ r) :
      ‖MvPolynomial.eval X (B m)‖ ≤ u m := by
    cases m with
    | zero => simp [u, hB0]
    | succ n =>
      simpa [u] using homogeneous_polynomial_eval_norm_geometric
        (B (n+1)) (hB n) hD hr (hC n) X hX
  refine ⟨?_, HasSumUniformlyOn.of_norm_le_summable hu hbound,
    tendstoUniformlyOn_tsum_nat hu hbound⟩
  intro X hX
  have habs : Summable (fun m => ‖MvPolynomial.eval X (B m)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => hbound m X hX) hu
  have hs : Summable (fun m => MvPolynomial.eval X (B m)) := habs.of_norm
  have heq : (∑' m, MvPolynomial.eval X (B m)) =
      (∑' n, MvPolynomial.eval X (B (n+1))) := by
    rw [hs.tsum_eq_zero_add, hB0, map_zero, zero_add]
  refine ⟨habs, hs, heq, ?_⟩
  rw [heq]
  exact homogeneous_polynomial_series_norm_tsum_le (fun n => B (n+1)) hB hD hr hDr hC X hX

end TheoremT.Continuum
