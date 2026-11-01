import KSRealPolynomialSeriesData_v1

/-! Pass the exact finite KS identity to the actual infinite polynomial sum.
Summability of the input evaluated on this KS preimage is derived from the
two output majorants. No identification with a physical Taylor series is
assumed or concluded beyond this specified polynomial input family. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum

theorem ks_real_polynomial_series_uniform_convergence
    (P : ℕ → MvPolynomial (Fin 4) ℂ)
    (hP : ∀ m, (P m).IsHomogeneous (2*m))
    (hbal : ∀ m d, d ∈ (ksRealPolynomialToSpinor (P m)).support → d 0+d 1=d 2+d 3)
    {M b r : ℝ} (hM : 0 ≤ M) (hb : 0 ≤ b) (hr : 0 ≤ r) (hDr : (32*b^2)*r < 1)
    (hc : ∀ m d, d ∈ (P m).support → ‖(P m).coeff d‖ ≤ M*b^(2*m)) :
    HasSumUniformlyOn (fun m X => MvPolynomial.eval X (ksRealPolynomialDescentA (P m)))
      (ksRealPolynomialSeriesA P) (complexClosedPolydisc (Fin 3) r) ∧
    HasSumUniformlyOn (fun n X => MvPolynomial.eval X (ksRealPolynomialDescentB (P (n+1))))
      (ksRealPolynomialSeriesB P) (complexClosedPolydisc (Fin 3) r) := by
  obtain ⟨hA,hB,hB0,hLA,hLB⟩ := ks_real_polynomial_series_data P hP hbal hM hb hc
  refine ⟨homogeneous_polynomial_series_hasSumUniformlyOn _ hA (by positivity) hr hDr hLA, ?_⟩
  exact (shifted_homogeneous_polynomial_series_closed_polydisc _ hB
    (by positivity) hr hDr (fun n => hLB (n+1))).2.1

theorem ks_real_polynomial_series_physical_descent
    (P : ℕ → MvPolynomial (Fin 4) ℂ)
    (hP : ∀ m, (P m).IsHomogeneous (2*m))
    (hbal : ∀ m d, d ∈ (ksRealPolynomialToSpinor (P m)).support → d 0+d 1=d 2+d 3)
    {M b r : ℝ} (hM : 0 ≤ M) (hb : 0 ≤ b) (hr : 0 ≤ r) (hDr : (32*b^2)*r < 1)
    (hc : ∀ m d, d ∈ (P m).support → ‖(P m).coeff d‖ ≤ M*b^(2*m))
    (y : KSSpace) (hy : (fun i => (ksMap y i : ℂ)) ∈ complexClosedPolydisc (Fin 3) r) :
    Summable (fun m => ‖MvPolynomial.eval (fun i => (y i : ℂ)) (P m)‖) ∧
    Summable (fun m => MvPolynomial.eval (fun i => (y i : ℂ)) (P m)) ∧
    (∑' m, MvPolynomial.eval (fun i => (y i : ℂ)) (P m)) =
      ksRealPolynomialSeriesA P (fun i => (ksMap y i : ℂ)) +
      (‖y‖^2 : ℝ)*ksRealPolynomialSeriesB P (fun i => (ksMap y i : ℂ)) := by
  obtain ⟨hA,hB,hB0,hLA,hLB⟩ := ks_real_polynomial_series_data P hP hbal hM hb hc
  let X : Fin 3 → ℂ := fun i => (ksMap y i : ℂ)
  let c : ℂ := (‖y‖^2 : ℝ)
  have hAs := homogeneous_polynomial_series_summable_norm
    (fun m => ksRealPolynomialDescentA (P m)) hA (by positivity) hr hDr hLA X hy
  have hBs := (odd_homogeneous_polynomial_series_zero_first
    (fun m => ksRealPolynomialDescentB (P m)) hB0 hB
    (by positivity) hr hDr (fun n => hLB (n+1))).1 X hy
  have hterm (m : ℕ) : MvPolynomial.eval (fun i => (y i : ℂ)) (P m) =
      MvPolynomial.eval X (ksRealPolynomialDescentA (P m)) +
      c*MvPolynomial.eval X (ksRealPolynomialDescentB (P m)) :=
    ks_real_polynomial_physical_descent (P m) (hbal m) y
  have habs : Summable (fun m => ‖MvPolynomial.eval (fun i => (y i : ℂ)) (P m)‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun m => ?_) (hAs.add (hBs.1.mul_left ‖c‖))
    rw [hterm]
    exact (norm_add_le _ _).trans_eq (by rw [norm_mul])
  refine ⟨habs,habs.of_norm,?_⟩
  calc
    _ = ∑' m, (MvPolynomial.eval X (ksRealPolynomialDescentA (P m)) +
        c*MvPolynomial.eval X (ksRealPolynomialDescentB (P m))) := tsum_congr hterm
    _ = (∑' m, MvPolynomial.eval X (ksRealPolynomialDescentA (P m))) +
        ∑' m, c*MvPolynomial.eval X (ksRealPolynomialDescentB (P m)) :=
      Summable.tsum_add hAs.of_norm (hBs.2.1.mul_left c)
    _ = _ := by rw [tsum_mul_left,hBs.2.2.1]; rfl

end TheoremT.Continuum
