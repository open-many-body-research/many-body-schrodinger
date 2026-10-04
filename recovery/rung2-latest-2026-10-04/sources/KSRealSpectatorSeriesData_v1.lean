import KSRealPolynomialSeriesData_v1
import HomogeneousSpectatorAnisotropicAnalytic_v1
import ShiftedHomogeneousSpectatorSeries_v1

/-! Actual finite KS descent applied to every member of a prescribed
radial-degree/spectator-multiindex family. The output double-series are
jointly analytic with the two separate rates. Physical Taylor extraction
and inherited circle invariance are not assumptions hidden in these names. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum
variable {d : ℕ}

def ksRealSpectatorFamilyA (P : ℕ → (Fin d → ℕ) → MvPolynomial (Fin 4) ℂ)
    (m : ℕ) (γ : Fin d → ℕ) : MvPolynomial (Fin 3) ℂ :=
  ksRealPolynomialDescentA (P m γ)

def ksRealSpectatorFamilyB (P : ℕ → (Fin d → ℕ) → MvPolynomial (Fin 4) ℂ)
    (n : ℕ) (γ : Fin d → ℕ) : MvPolynomial (Fin 3) ℂ :=
  ksRealPolynomialDescentB (P (n+1) γ)

theorem ks_real_spectator_series_data
    (P : ℕ → (Fin d → ℕ) → MvPolynomial (Fin 4) ℂ)
    (hP : ∀ m γ, (P m γ).IsHomogeneous (2*m))
    (hbal : ∀ m γ e, e ∈ (ksRealPolynomialToSpinor (P m γ)).support → e 0+e 1=e 2+e 3)
    {M b S : ℝ} (hM : 0 ≤ M) (hb : 0 ≤ b) (hS : 0 ≤ S)
    (hc : ∀ m γ e, e ∈ (P m γ).support →
      ‖(P m γ).coeff e‖ ≤ M*b^(2*m)*S^(∑ i : Fin d, γ i)) :
    (∀ m γ, (ksRealSpectatorFamilyA P m γ).IsHomogeneous m) ∧
    (∀ n γ, (ksRealSpectatorFamilyB P n γ).IsHomogeneous n) ∧
    (∀ γ, ksRealPolynomialDescentB (P 0 γ) = 0) ∧
    (∀ m γ, polynomialCoeffL1 (ksRealSpectatorFamilyA P m γ) ≤
      M*(32*b^2)^m*S^(∑ i : Fin d, γ i)) ∧
    (∀ n γ, polynomialCoeffL1 (ksRealSpectatorFamilyB P n γ) ≤
      M*(32*b^2)^(n+1)*S^(∑ i : Fin d, γ i)) := by
  have hdata (γ : Fin d → ℕ) := ks_real_polynomial_series_data (fun m => P m γ)
    (fun m => hP m γ) (fun m => hbal m γ)
    (mul_nonneg hM (pow_nonneg hS _)) hb
    (fun m e he => by simpa [mul_assoc,mul_comm,mul_left_comm] using hc m γ e he)
  refine ⟨fun m γ => (hdata γ).1 m, fun n γ => (hdata γ).2.1 n,
    fun γ => (hdata γ).2.2.1, ?_, ?_⟩
  · intro m γ
    simpa [ksRealSpectatorFamilyA,mul_assoc,mul_comm,mul_left_comm] using (hdata γ).2.2.2.1 m
  · intro n γ
    simpa [ksRealSpectatorFamilyB,mul_assoc,mul_comm,mul_left_comm] using (hdata γ).2.2.2.2 (n+1)

theorem ks_real_spectator_series_analytic
    (P : ℕ → (Fin d → ℕ) → MvPolynomial (Fin 4) ℂ)
    (hP : ∀ m γ, (P m γ).IsHomogeneous (2*m))
    (hbal : ∀ m γ e, e ∈ (ksRealPolynomialToSpinor (P m γ)).support → e 0+e 1=e 2+e 3)
    {M b S : ℝ} (hM : 0 ≤ M) (hb : 0 ≤ b) (hS : 0 ≤ S)
    (hc : ∀ m γ e, e ∈ (P m γ).support →
      ‖(P m γ).coeff e‖ ≤ M*b^(2*m)*S^(∑ i : Fin d, γ i)) :
    AnalyticOnNhd ℂ (homogeneousSpectatorSum (ksRealSpectatorFamilyA P))
      {z : Fin 3 ⊕ Fin d → ℂ | (32*b^2)*‖fun i : Fin 3 => z (.inl i)‖ < 1 ∧
        S*‖fun i : Fin d => z (.inr i)‖ < 1} ∧
    AnalyticOnNhd ℂ (homogeneousSpectatorSum (ksRealSpectatorFamilyB P))
      {z : Fin 3 ⊕ Fin d → ℂ | (32*b^2)*‖fun i : Fin 3 => z (.inl i)‖ < 1 ∧
        S*‖fun i : Fin d => z (.inr i)‖ < 1} := by
  obtain ⟨hA,hB,hB0,hLA,hLB⟩ := ks_real_spectator_series_data P hP hbal hM hb hS hc
  refine ⟨homogeneous_spectator_sum_analytic_anisotropic _ hA hM (by positivity) hS hLA, ?_⟩
  apply homogeneous_spectator_sum_analytic_anisotropic _ hB
    (mul_nonneg hM (show 0 ≤ 32*b^2 by positivity)) (by positivity) hS
  intro n γ
  calc
    _ ≤ M*(32*b^2)^(n+1)*S^(∑ i : Fin d, γ i) := hLB n γ
    _ = (M*(32*b^2))*(32*b^2)^n*S^(∑ i : Fin d, γ i) := by rw [pow_succ]; ring

theorem ks_real_spectator_series_norm_bounds
    (P : ℕ → (Fin d → ℕ) → MvPolynomial (Fin 4) ℂ)
    (hP : ∀ m γ, (P m γ).IsHomogeneous (2*m))
    (hbal : ∀ m γ e, e ∈ (ksRealPolynomialToSpinor (P m γ)).support → e 0+e 1=e 2+e 3)
    {M b S r h : ℝ} (hM : 0 ≤ M) (hb : 0 ≤ b) (hS : 0 ≤ S)
    (hr : 0 ≤ r) (hh : 0 ≤ h) (hDr : (32*b^2)*r < 1) (hSh : S*h < 1)
    (hc : ∀ m γ e, e ∈ (P m γ).support →
      ‖(P m γ).coeff e‖ ≤ M*b^(2*m)*S^(∑ i : Fin d, γ i))
    (X : Fin 3 → ℂ) (s : Fin d → ℂ)
    (hX : X ∈ complexClosedPolydisc (Fin 3) r) (hs : s ∈ complexClosedPolydisc (Fin d) h) :
    ‖homogeneousSpectatorSum (ksRealSpectatorFamilyA P) (Sum.elim X s)‖ ≤
      M/((1-(32*b^2)*r)*(1-S*h)^d) ∧
    ‖homogeneousSpectatorSum (ksRealSpectatorFamilyB P) (Sum.elim X s)‖ ≤
      (M*(32*b^2))/((1-(32*b^2)*r)*(1-S*h)^d) := by
  obtain ⟨hA,hB,hB0,hLA,hLB⟩ := ks_real_spectator_series_data P hP hbal hM hb hS hc
  exact ⟨((homogeneous_spectator_series_closed_polydiscs _ hA hM (by positivity) hr hS hh
      hDr hSh hLA).1 (X,s) ⟨hX,hs⟩).2.2,
    ((shifted_homogeneous_spectator_series_closed_polydiscs _ hB hM (by positivity) hr hS hh
      hDr hSh hLB).1 (X,s) ⟨hX,hs⟩).2.2⟩

end TheoremT.Continuum
