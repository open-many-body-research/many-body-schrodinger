import HomogeneousSpectatorAnisotropicAnalytic_v1
import MvPolynomialCoefficientL1Scaling_v1

/-! Actual scalar power series with finitely many spectator variables.
The radial coefficient is unchanged: the auxiliary polynomial is literally
C(c) X_0^m. The domain retains separate radial and spectator radii. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum
variable {d : ℕ}

def scalarSpectatorPolynomialFamily (c : ℕ → (Fin d → ℕ) → ℂ)
    (m : ℕ) (γ : Fin d → ℕ) : MvPolynomial (Fin 3) ℂ :=
  MvPolynomial.C (c m γ) * MvPolynomial.X 0 ^ m

theorem scalarSpectatorPolynomialFamily_isHomogeneous
    (c : ℕ → (Fin d → ℕ) → ℂ) (m : ℕ) (γ : Fin d → ℕ) :
    (scalarSpectatorPolynomialFamily c m γ).IsHomogeneous m :=
  (MvPolynomial.isHomogeneous_X_pow (0 : Fin 3) m).C_mul _

theorem scalarSpectatorPolynomialFamily_coeffL1_le
    (c : ℕ → (Fin d → ℕ) → ℂ) (m : ℕ) (γ : Fin d → ℕ) :
    polynomialCoeffL1 (scalarSpectatorPolynomialFamily c m γ) ≤ ‖c m γ‖ := by
  unfold scalarSpectatorPolynomialFamily
  rw [polynomialCoeffL1_C_mul]
  have h := polynomialCoeffL1_pow (MvPolynomial.X (0 : Fin 3)) m
  rw [polynomialCoeffL1_X, one_pow] at h
  simpa only [mul_one] using mul_le_mul_of_nonneg_left h (norm_nonneg (c m γ))

def scalarSpectatorTerm (c : ℕ → (Fin d → ℕ) → ℂ)
    (k : ℕ × (Fin d → ℕ)) (z : ℂ × (Fin d → ℂ)) : ℂ :=
  c k.1 k.2 * z.1 ^ k.1 * ∏ i : Fin d, z.2 i ^ k.2 i

def scalarSpectatorSum (c : ℕ → (Fin d → ℕ) → ℂ)
    (z : ℂ × (Fin d → ℂ)) : ℂ := ∑' k, scalarSpectatorTerm c k z

theorem scalarSpectatorTerm_eq (c : ℕ → (Fin d → ℕ) → ℂ)
    (k : ℕ × (Fin d → ℕ)) (z : ℂ × (Fin d → ℂ)) :
    homogeneousSpectatorTerm (scalarSpectatorPolynomialFamily c) k
      ((fun _ : Fin 3 => z.1), z.2) = scalarSpectatorTerm c k z := by
  simp [homogeneousSpectatorTerm, scalarSpectatorPolynomialFamily, scalarSpectatorTerm]

theorem scalarSpectatorSum_eq (c : ℕ → (Fin d → ℕ) → ℂ)
    (z : ℂ × (Fin d → ℂ)) :
    homogeneousSpectatorSum (scalarSpectatorPolynomialFamily c)
      (Sum.elim (fun _ : Fin 3 => z.1) z.2) = scalarSpectatorSum c z := by
  unfold homogeneousSpectatorSum scalarSpectatorSum
  apply tsum_congr
  intro k
  exact scalarSpectatorTerm_eq c k z

theorem scalar_spectator_sum_analytic (c : ℕ → (Fin d → ℕ) → ℂ)
    {M D S : ℝ} (hM : 0 ≤ M) (hD : 0 ≤ D) (hS : 0 ≤ S)
    (hc : ∀ m γ, ‖c m γ‖ ≤ M*D^m*S^(∑ i : Fin d, γ i)) :
    AnalyticOnNhd ℂ (scalarSpectatorSum c)
      {z : ℂ × (Fin d → ℂ) | D*‖z.1‖ < 1 ∧ S*‖z.2‖ < 1} := by
  have hF := homogeneous_spectator_sum_analytic_anisotropic
    (scalarSpectatorPolynomialFamily c) (scalarSpectatorPolynomialFamily_isHomogeneous c)
    hM hD hS (fun m γ => (scalarSpectatorPolynomialFamily_coeffL1_le c m γ).trans (hc m γ))
  intro z hz
  have hz' : D*‖fun _ : Fin 3 => z.1‖ < 1 ∧ S*‖z.2‖ < 1 := by
    simpa using hz
  have hmap : AnalyticAt ℂ
      (fun t : ℂ × (Fin d → ℂ) => Sum.elim (fun _ : Fin 3 => t.1) t.2) z := by
    apply AnalyticAt.pi
    intro i
    cases i with
    | inl i => exact (ContinuousLinearMap.fst ℂ ℂ (Fin d → ℂ)).analyticAt z
    | inr i =>
      exact ((ContinuousLinearMap.proj i : (Fin d → ℂ) →L[ℂ] ℂ).comp
        (ContinuousLinearMap.snd ℂ ℂ (Fin d → ℂ))).analyticAt z
  have hh := AnalyticAt.comp_of_eq
    (g := homogeneousSpectatorSum (scalarSpectatorPolynomialFamily c)) (hF _ hz') hmap rfl
  have heq : (fun t : ℂ × (Fin d → ℂ) =>
      homogeneousSpectatorSum (scalarSpectatorPolynomialFamily c)
        (Sum.elim (fun _ : Fin 3 => t.1) t.2)) = scalarSpectatorSum c := by
    funext t
    exact scalarSpectatorSum_eq c t
  exact heq ▸ hh

theorem scalar_spectator_series_closed_polydiscs (c : ℕ → (Fin d → ℕ) → ℂ)
    {M D r S h : ℝ} (hM : 0 ≤ M) (hD : 0 ≤ D) (hr : 0 ≤ r)
    (hS : 0 ≤ S) (hh : 0 ≤ h) (hDr : D*r < 1) (hSh : S*h < 1)
    (hc : ∀ m γ, ‖c m γ‖ ≤ M*D^m*S^(∑ i : Fin d, γ i)) :
    (∀ z ∈ {z : ℂ × (Fin d → ℂ) | ‖z.1‖ ≤ r ∧ ∀ i, ‖z.2 i‖ ≤ h},
      Summable (fun k => ‖scalarSpectatorTerm c k z‖) ∧
      Summable (fun k => scalarSpectatorTerm c k z) ∧
      ‖scalarSpectatorSum c z‖ ≤ M/((1-D*r)*(1-S*h)^d)) ∧
    HasSumUniformlyOn (scalarSpectatorTerm c) (scalarSpectatorSum c)
      {z : ℂ × (Fin d → ℂ) | ‖z.1‖ ≤ r ∧ ∀ i, ‖z.2 i‖ ≤ h} := by
  have hL := fun m γ => (scalarSpectatorPolynomialFamily_coeffL1_le c m γ).trans (hc m γ)
  have hu := homogeneous_spectator_majorant_hasSum d hM hD hr hS hh hDr hSh
  have hb := homogeneous_spectator_term_norm_bound
    (scalarSpectatorPolynomialFamily c) (scalarSpectatorPolynomialFamily_isHomogeneous c) hr hh hL
  have hb' (k : ℕ × (Fin d → ℕ)) (z : ℂ × (Fin d → ℂ))
      (hz : z ∈ {z : ℂ × (Fin d → ℂ) | ‖z.1‖ ≤ r ∧ ∀ i, ‖z.2 i‖ ≤ h}) :
      ‖scalarSpectatorTerm c k z‖ ≤ homogeneousSpectatorMajorant M D r S h k := by
    have hx : ((fun _ : Fin 3 => z.1), z.2) ∈
        complexClosedPolydisc (Fin 3) r ×ˢ complexClosedPolydisc (Fin d) h :=
      ⟨fun _ => hz.1, hz.2⟩
    simpa only [scalarSpectatorTerm_eq] using hb k _ hx
  refine ⟨?_, HasSumUniformlyOn.of_norm_le_summable hu.summable hb'⟩
  intro z hz
  have habs := Summable.of_nonneg_of_le (fun k => norm_nonneg (scalarSpectatorTerm c k z))
    (fun k => hb' k z hz) hu.summable
  refine ⟨habs, habs.of_norm, ?_⟩
  calc
    _ ≤ ∑' k, ‖scalarSpectatorTerm c k z‖ := norm_tsum_le_tsum_norm habs
    _ ≤ ∑' k, homogeneousSpectatorMajorant M D r S h k :=
      habs.tsum_le_tsum (fun k => hb' k z hz) hu.summable
    _ = _ := hu.tsum_eq

end TheoremT.Continuum
