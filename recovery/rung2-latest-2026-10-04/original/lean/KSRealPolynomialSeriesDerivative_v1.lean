import KSRealPolynomialSeriesData_v1
import HomogeneousPolynomialSeriesDerivative_v1

/-! All-order complex Frechet estimates for the literal prescribed-family
KS descent coefficients. The input family and its balance are explicit;
these bounds do not assert that the physical lift has already supplied it. -/
noncomputable section
set_option autoImplicit false
namespace TheoremT.Continuum

theorem ks_real_polynomial_series_half_domain_factorial_bounds
    (P : ℕ → MvPolynomial (Fin 4) ℂ)
    (hP : ∀ m, (P m).IsHomogeneous (2*m))
    (hbal : ∀ m d, d ∈ (ksRealPolynomialToSpinor (P m)).support → d 0+d 1=d 2+d 3)
    {M b : ℝ} (hM : 0 ≤ M) (hb : 0 ≤ b)
    (hc : ∀ m d, d ∈ (P m).support → ‖(P m).coeff d‖ ≤ M*b^(2*m))
    (X : Fin 3 → ℂ) (hX : (32*b^2)*‖X‖ ≤ 1/2) (k : ℕ) :
    ‖iteratedFDeriv ℂ k (ksRealPolynomialSeriesA P) X‖ ≤
      (2*M)*(2*(32*b^2))^k*(k.factorial : ℝ) ∧
    ‖iteratedFDeriv ℂ k (ksRealPolynomialSeriesB P) X‖ ≤
      (2*M*(32*b^2))*(2*(32*b^2))^k*(k.factorial : ℝ) := by
  obtain ⟨hA,hB,hB0,hLA,hLB⟩ := ks_real_polynomial_series_data P hP hbal hM hb hc
  exact ⟨homogeneous_polynomial_series_half_domain_factorial_bound
    _ hA hM (by positivity) hLA X hX k,
    shifted_homogeneous_polynomial_series_half_domain_factorial_bound
      _ hB hM (by positivity) (fun n => hLB (n+1)) X hX k⟩

end TheoremT.Continuum
