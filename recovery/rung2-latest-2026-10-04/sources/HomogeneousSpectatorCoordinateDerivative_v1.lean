import HomogeneousSpectatorNormalizedDerivative_v1
import SpectatorScalingIteratedDerivativeWord_v1

/-! Explicit coordinate-word derivative bounds for the original joint sum.
The actual block-linear chain rule restores each direction's scale factor
separately. Positive D,S and the smaller quarter polydisc are explicit;
the coarse prefactor is not the original mixed Cauchy constant. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum
variable {d : ℕ}

theorem homogeneous_spectator_coordinate_word_factorial_bound
    (A : ℕ → (Fin d → ℕ) → MvPolynomial (Fin 3) ℂ)
    (hA : ∀ m γ, (A m γ).IsHomogeneous m) {M D S : ℝ}
    (hM : 0 ≤ M) (hD : 0 < D) (hS : 0 < S)
    (hL : ∀ m γ, polynomialCoeffL1 (A m γ) ≤ M*D^m*S^(∑ i : Fin d, γ i))
    (z : Fin 3 ⊕ Fin d → ℂ)
    (hX : D*‖fun i : Fin 3 => z (.inl i)‖ ≤ 1/4)
    (hs : S*‖fun i : Fin d => z (.inr i)‖ ≤ 1/4)
    (k : ℕ) (w : Fin k → Fin 3 ⊕ Fin d) :
    ‖iteratedFDeriv ℂ k (homogeneousSpectatorSum A) z
      (fun j => Pi.single (w j) (1 : ℂ))‖ ≤
      ((2*(M*2^d))*4^k*(k.factorial : ℝ))*
        ∏ j, ‖spectatorScalingCoefficient D S (w j)‖ := by
  let A' := rescaledHomogeneousSpectatorFamily A D⁻¹ S⁻¹
  have hA' : ∀ m γ, (A' m γ).IsHomogeneous m :=
    rescaledHomogeneousSpectatorFamily_isHomogeneous A hA _ _
  have hL' (m : ℕ) (γ : Fin d → ℕ) : polynomialCoeffL1 (A' m γ) ≤ M*(1:ℝ)^(m+∑i, γ i) := by
    simpa only [one_pow,mul_one] using polynomialCoeffL1_normalizedHomogeneousSpectatorFamily
      A hM hD hS hL m γ
  have hnorm := spectatorScalingMap_norm_le_of_blocks hD.le hS.le (by norm_num) z hX hs
  have hana : AnalyticAt ℂ (homogeneousSpectatorSum A') (spectatorScalingMap D S z) :=
    homogeneous_spectator_sum_analytic_isotropic A' hA' hM (by norm_num) hL' _
      (by change 1*‖spectatorScalingMap D S z‖ < 1; linarith)
  have hEq : homogeneousSpectatorSum A = homogeneousSpectatorSum A' ∘ spectatorScalingMap D S := by
    funext v
    exact homogeneousSpectatorSum_normalized_eq A hA (ne_of_gt hD) (ne_of_gt hS) v
  rw [hEq]
  exact (spectatorScaling_iteratedFDeriv_word_norm_le D S (homogeneousSpectatorSum A') z k w
    hana.contDiffAt).trans (mul_le_mul_of_nonneg_right
      (homogeneous_spectator_normalized_quarter_domain_factorial_bound A hA hM hD hS hL z hX hs k)
      (Finset.prod_nonneg fun _ _ => norm_nonneg _))

end TheoremT.Continuum
