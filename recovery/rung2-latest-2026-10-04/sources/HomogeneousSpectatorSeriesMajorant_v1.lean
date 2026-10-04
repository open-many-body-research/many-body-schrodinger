import HomogeneousPolynomialEvaluationBound_v1
import SpectatorGeometricMultiindexSum_v1

/-! Literal polynomial/spectator terms and their two-factor geometric majorant.
The index is the actual product Nat × (Fin d → Nat). -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum

def homogeneousSpectatorTerm {d : ℕ}
    (A : ℕ → (Fin d → ℕ) → MvPolynomial (Fin 3) ℂ)
    (k : ℕ × (Fin d → ℕ)) (z : (Fin 3 → ℂ) × (Fin d → ℂ)) : ℂ :=
  MvPolynomial.eval z.1 (A k.1 k.2) * ∏ i : Fin d, z.2 i ^ k.2 i

def homogeneousSpectatorMajorant {d : ℕ} (M D r S h : ℝ)
    (k : ℕ × (Fin d → ℕ)) : ℝ :=
  (M*(D*r)^k.1)*spectatorGeometricWeight (fun _ : Fin d => S*h) k.2

theorem spectator_monomial_norm_bound {d : ℕ} (s : Fin d → ℂ) (γ : Fin d → ℕ)
    {h : ℝ} (hh : 0 ≤ h) (hs : s ∈ complexClosedPolydisc (Fin d) h) :
    ‖∏ i : Fin d, s i ^ γ i‖ ≤ h^(∑ i : Fin d, γ i) := by
  rw [norm_prod, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
  intro i hi
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hs i) _

theorem homogeneous_spectator_term_norm_bound {d : ℕ}
    (A : ℕ → (Fin d → ℕ) → MvPolynomial (Fin 3) ℂ)
    (hA : ∀ m γ, (A m γ).IsHomogeneous m)
    {M D r S h : ℝ} (hr : 0 ≤ r) (hh : 0 ≤ h)
    (hL : ∀ m γ, polynomialCoeffL1 (A m γ) ≤ M*D^m*S^(∑ i : Fin d, γ i))
    (k : ℕ × (Fin d → ℕ)) (z : (Fin 3 → ℂ) × (Fin d → ℂ))
    (hz : z ∈ complexClosedPolydisc (Fin 3) r ×ˢ complexClosedPolydisc (Fin d) h) :
    ‖homogeneousSpectatorTerm A k z‖ ≤ homogeneousSpectatorMajorant M D r S h k := by
  have he := homogeneous_polynomial_eval_norm_bound (A k.1 k.2) (hA k.1 k.2) z.1 hr hz.1
  have hm := spectator_monomial_norm_bound z.2 k.2 hh hz.2
  rw [homogeneousSpectatorTerm, norm_mul]
  calc
    _ ≤ (polynomialCoeffL1 (A k.1 k.2)*r^k.1)*h^(∑ i : Fin d, k.2 i) :=
      mul_le_mul he hm (norm_nonneg _) (mul_nonneg (polynomialCoeffL1_nonneg _) (pow_nonneg hr _))
    _ ≤ ((M*D^k.1*S^(∑ i : Fin d, k.2 i))*r^k.1)*h^(∑ i : Fin d, k.2 i) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hL k.1 k.2) (pow_nonneg hr _)) (pow_nonneg hh _)
    _ = homogeneousSpectatorMajorant M D r S h k := by
      unfold homogeneousSpectatorMajorant spectatorGeometricWeight
      rw [Finset.prod_pow_eq_pow_sum, mul_pow, mul_pow]
      ring

theorem homogeneous_spectator_majorant_hasSum (d : ℕ)
    {M D r S h : ℝ} (hM : 0 ≤ M) (hD : 0 ≤ D) (hr : 0 ≤ r)
    (hS : 0 ≤ S) (hh : 0 ≤ h) (hDr : D*r < 1) (hSh : S*h < 1) :
    HasSum (homogeneousSpectatorMajorant (d := d) M D r S h)
      (M/((1-D*r)*(1-S*h)^d)) := by
  have ha := (hasSum_geometric_of_lt_one (mul_nonneg hD hr) hDr).mul_left M
  have hb : HasSum (spectatorGeometricWeight (fun _ : Fin d => S*h)) (((1-S*h)^d)⁻¹) := by
    simpa [← inv_pow] using spectator_geometric_hasSum d (fun _ => S*h)
      (fun _ => mul_nonneg hS hh) (fun _ => hSh)
  have hp := ha.mul hb (ha.summable.mul_of_nonneg hb.summable
    (fun m => mul_nonneg hM (pow_nonneg (mul_nonneg hD hr) m))
    (fun γ => spectatorGeometricWeight_nonneg _ (fun _ => mul_nonneg hS hh) γ))
  change HasSum (fun k : ℕ × (Fin d → ℕ) =>
    (M*(D*r)^k.1)*spectatorGeometricWeight (fun _ : Fin d => S*h) k.2) _
  simpa only [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm] using hp

theorem homogeneous_spectator_majorant_summable {d : ℕ}
    {M D r S h : ℝ} (hM : 0 ≤ M) (hD : 0 ≤ D) (hr : 0 ≤ r)
    (hS : 0 ≤ S) (hh : 0 ≤ h) (hDr : D*r < 1) (hSh : S*h < 1) :
    Summable (homogeneousSpectatorMajorant (d := d) M D r S h) :=
  (homogeneous_spectator_majorant_hasSum d hM hD hr hS hh hDr hSh).summable

end TheoremT.Continuum
