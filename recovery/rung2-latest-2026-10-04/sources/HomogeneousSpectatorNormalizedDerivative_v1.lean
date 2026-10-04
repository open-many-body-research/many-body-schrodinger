import HomogeneousSpectatorSeriesDerivative_v1
import SpectatorScalingMap_v1

/-! Actual block normalization for explicit derivative estimates.
The two rates are positive here, as stated, so their inverses are defined
without a limiting convention. The conclusion estimates the derivative
of the literal normalized series at the normalized point; the separate
coordinate direction factors are restored in the subsequent linear chain
rule theorem. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum
variable {d : ℕ}

theorem homogeneousSpectatorSum_normalized_eq
    (A : ℕ → (Fin d → ℕ) → MvPolynomial (Fin 3) ℂ)
    (hA : ∀ m γ, (A m γ).IsHomogeneous m) {D S : ℝ}
    (hD : D ≠ 0) (hS : S ≠ 0) (z : Fin 3 ⊕ Fin d → ℂ) :
    homogeneousSpectatorSum A z =
      homogeneousSpectatorSum (rescaledHomogeneousSpectatorFamily A D⁻¹ S⁻¹)
        (spectatorScalingMap D S z) := by
  rw [homogeneousSpectatorSum_rescaling A hA]
  have hi := spectatorScalingMap_inverse_cancel (inv_ne_zero hD) (inv_ne_zero hS) z
  simpa only [inv_inv] using (congrArg (homogeneousSpectatorSum A) hi).symm

theorem polynomialCoeffL1_normalizedHomogeneousSpectatorFamily
    (A : ℕ → (Fin d → ℕ) → MvPolynomial (Fin 3) ℂ) {M D S : ℝ}
    (hM : 0 ≤ M) (hD : 0 < D) (hS : 0 < S)
    (hL : ∀ m γ, polynomialCoeffL1 (A m γ) ≤ M*D^m*S^(∑ i : Fin d, γ i))
    (m : ℕ) (γ : Fin d → ℕ) :
    polynomialCoeffL1 (rescaledHomogeneousSpectatorFamily A D⁻¹ S⁻¹ m γ) ≤ M := by
  simpa only [one_pow,mul_one] using polynomialCoeffL1_rescaledHomogeneousSpectatorFamily
    A hM hD.le hS.le (inv_nonneg.mpr hD.le) (inv_nonneg.mpr hS.le)
    (show D*D⁻¹ ≤ (1:ℝ) by simp [ne_of_gt hD])
    (show S*S⁻¹ ≤ (1:ℝ) by simp [ne_of_gt hS]) hL m γ

theorem spectatorScalingMap_norm_le_of_blocks {D S q : ℝ}
    (hD : 0 ≤ D) (hS : 0 ≤ S) (hq : 0 ≤ q) (z : Fin 3 ⊕ Fin d → ℂ)
    (hX : D*‖fun i : Fin 3 => z (.inl i)‖ ≤ q)
    (hs : S*‖fun i : Fin d => z (.inr i)‖ ≤ q) :
    ‖spectatorScalingMap D S z‖ ≤ q := by
  apply (pi_norm_le_iff_of_nonneg hq).mpr
  intro i
  cases i with
  | inl i =>
    simp only [spectatorScalingMap,Sum.elim_inl,norm_mul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg hD]
    exact (mul_le_mul_of_nonneg_left (norm_le_pi_norm (fun i : Fin 3 => z (.inl i)) i) hD).trans hX
  | inr i =>
    simp only [spectatorScalingMap,Sum.elim_inr,norm_mul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg hS]
    exact (mul_le_mul_of_nonneg_left (norm_le_pi_norm (fun i : Fin d => z (.inr i)) i) hS).trans hs

theorem homogeneous_spectator_normalized_quarter_domain_factorial_bound
    (A : ℕ → (Fin d → ℕ) → MvPolynomial (Fin 3) ℂ)
    (hA : ∀ m γ, (A m γ).IsHomogeneous m) {M D S : ℝ}
    (hM : 0 ≤ M) (hD : 0 < D) (hS : 0 < S)
    (hL : ∀ m γ, polynomialCoeffL1 (A m γ) ≤ M*D^m*S^(∑ i : Fin d, γ i))
    (z : Fin 3 ⊕ Fin d → ℂ)
    (hX : D*‖fun i : Fin 3 => z (.inl i)‖ ≤ 1/4)
    (hs : S*‖fun i : Fin d => z (.inr i)‖ ≤ 1/4) (k : ℕ) :
    ‖iteratedFDeriv ℂ k
      (homogeneousSpectatorSum (rescaledHomogeneousSpectatorFamily A D⁻¹ S⁻¹))
      (spectatorScalingMap D S z)‖ ≤ (2*(M*2^d))*4^k*(k.factorial : ℝ) := by
  have hnorm := spectatorScalingMap_norm_le_of_blocks hD.le hS.le (by norm_num) z hX hs
  simpa only [one_pow,mul_one,one_mul] using homogeneous_spectator_series_quarter_domain_factorial_bound
    (rescaledHomogeneousSpectatorFamily A D⁻¹ S⁻¹)
    (rescaledHomogeneousSpectatorFamily_isHomogeneous A hA _ _) hM (show 0 ≤ (1:ℝ) by norm_num)
    (fun m γ => by simpa only [one_pow,mul_one] using
      polynomialCoeffL1_normalizedHomogeneousSpectatorFamily A hM hD hS hL m γ)
    (spectatorScalingMap D S z) (by simpa only [one_mul] using hnorm) k

end TheoremT.Continuum
