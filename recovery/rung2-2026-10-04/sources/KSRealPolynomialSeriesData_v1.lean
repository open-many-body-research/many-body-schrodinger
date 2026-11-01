import KSRealPolynomialDescent_v1
import HomogeneousPolynomialSeriesAnalytic_v1
import OddHomogeneousPolynomialSeriesZeroFirst_v1

/-! The actual polynomial families emitted by finite real-coordinate KS
descent have the exact even/odd degrees and geometric coefficient bounds.
The input remains a specified homogeneous polynomial family with a balance
premise; no extraction of a physical Taylor family is asserted here. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum

def ksRealPolynomialSeriesA (P : ℕ → MvPolynomial (Fin 4) ℂ) (X : Fin 3 → ℂ) : ℂ :=
  ∑' m, MvPolynomial.eval X (ksRealPolynomialDescentA (P m))

def ksRealPolynomialSeriesB (P : ℕ → MvPolynomial (Fin 4) ℂ) (X : Fin 3 → ℂ) : ℂ :=
  ∑' n, MvPolynomial.eval X (ksRealPolynomialDescentB (P (n+1)))

theorem ks_real_polynomial_series_data
    (P : ℕ → MvPolynomial (Fin 4) ℂ)
    (hP : ∀ m, (P m).IsHomogeneous (2*m))
    (hbal : ∀ m d, d ∈ (ksRealPolynomialToSpinor (P m)).support → d 0+d 1=d 2+d 3)
    {M b : ℝ} (hM : 0 ≤ M) (hb : 0 ≤ b)
    (hc : ∀ m d, d ∈ (P m).support → ‖(P m).coeff d‖ ≤ M*b^(2*m)) :
    (∀ m, (ksRealPolynomialDescentA (P m)).IsHomogeneous m) ∧
    (∀ n, (ksRealPolynomialDescentB (P (n+1))).IsHomogeneous n) ∧
    ksRealPolynomialDescentB (P 0) = 0 ∧
    (∀ m, polynomialCoeffL1 (ksRealPolynomialDescentA (P m)) ≤ M*(32*b^2)^m) ∧
    (∀ m, polynomialCoeffL1 (ksRealPolynomialDescentB (P m)) ≤ M*(32*b^2)^m) := by
  have hhom (m : ℕ) := ks_real_polynomial_descent_homogeneous (hP m) (hbal m)
  have hnorm (m : ℕ) := polynomialCoeffL1_real_descent_geometric_bound
    (P m) (hP m) (hbal m) hM hb (hc m)
  refine ⟨fun m => (hhom m).1, ?_, (hhom 0).2.2 rfl, ?_, ?_⟩
  · intro n
    simpa only [Nat.add_sub_cancel] using (hhom (n+1)).2.1
  · intro m
    exact (le_add_of_nonneg_right (polynomialCoeffL1_nonneg _)).trans (hnorm m)
  · intro m
    exact (le_add_of_nonneg_left (polynomialCoeffL1_nonneg _)).trans (hnorm m)

theorem ks_real_polynomial_series_analytic
    (P : ℕ → MvPolynomial (Fin 4) ℂ)
    (hP : ∀ m, (P m).IsHomogeneous (2*m))
    (hbal : ∀ m d, d ∈ (ksRealPolynomialToSpinor (P m)).support → d 0+d 1=d 2+d 3)
    {M b : ℝ} (hM : 0 ≤ M) (hb : 0 ≤ b)
    (hc : ∀ m d, d ∈ (P m).support → ‖(P m).coeff d‖ ≤ M*b^(2*m)) :
    AnalyticOnNhd ℂ (ksRealPolynomialSeriesA P) {X : Fin 3 → ℂ | (32*b^2)*‖X‖ < 1} ∧
    AnalyticOnNhd ℂ (ksRealPolynomialSeriesB P) {X : Fin 3 → ℂ | (32*b^2)*‖X‖ < 1} := by
  obtain ⟨hA,hB,hB0,hLA,hLB⟩ := ks_real_polynomial_series_data P hP hbal hM hb hc
  exact ⟨homogeneous_polynomial_series_analyticOnNhd _ hA hM (by positivity) hLA,
    shifted_homogeneous_polynomial_series_analyticOnNhd _ hB hM (by positivity)
      (fun n => hLB (n+1))⟩

theorem ks_real_polynomial_series_norm_bounds
    (P : ℕ → MvPolynomial (Fin 4) ℂ)
    (hP : ∀ m, (P m).IsHomogeneous (2*m))
    (hbal : ∀ m d, d ∈ (ksRealPolynomialToSpinor (P m)).support → d 0+d 1=d 2+d 3)
    {M b r : ℝ} (hM : 0 ≤ M) (hb : 0 ≤ b) (hr : 0 ≤ r) (hDr : (32*b^2)*r < 1)
    (hc : ∀ m d, d ∈ (P m).support → ‖(P m).coeff d‖ ≤ M*b^(2*m))
    (X : Fin 3 → ℂ) (hX : X ∈ complexClosedPolydisc (Fin 3) r) :
    ‖ksRealPolynomialSeriesA P X‖ ≤ M/(1-(32*b^2)*r) ∧
    ‖ksRealPolynomialSeriesB P X‖ ≤ (M*(32*b^2))/(1-(32*b^2)*r) := by
  obtain ⟨hA,hB,hB0,hLA,hLB⟩ := ks_real_polynomial_series_data P hP hbal hM hb hc
  refine ⟨homogeneous_polynomial_series_norm_tsum_le _ hA (by positivity) hr hDr hLA X hX, ?_⟩
  exact ((shifted_homogeneous_polynomial_series_closed_polydisc _ hB
    (by positivity) hr hDr (fun n => hLB (n+1))).1 X hX).2.2

end TheoremT.Continuum
