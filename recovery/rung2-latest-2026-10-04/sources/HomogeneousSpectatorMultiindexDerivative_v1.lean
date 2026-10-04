import HomogeneousSpectatorCoordinateDerivative_v1
import MultiindexCoordinateWordCount_v1
import MultiindexFactorialDimensionBound_v1

/-! A literal coordinate multiindex derivative and an explicit bound for
the actual polynomial/spectator sum. The finite word is a fixed classical
representative with the prescribed coordinate multiplicities; no word
enumeration algorithm is claimed. The dimension loss converting total
factorials to multiindex factorials is displayed in the final rate. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum

def complexMultiindexDeriv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → ℂ) → ℂ) (α : ι → ℕ) (z : ι → ℂ) : ℂ :=
  iteratedFDeriv ℂ (∑ i, α i) f z
    (fun j => Pi.single (multiindexCoordinateWord α j) (1 : ℂ))

theorem homogeneous_spectator_multiindex_factorial_bound {d : ℕ}
    (A : ℕ → (Fin d → ℕ) → MvPolynomial (Fin 3) ℂ)
    (hA : ∀ m γ, (A m γ).IsHomogeneous m) {M D S : ℝ}
    (hM : 0 ≤ M) (hD : 0 < D) (hS : 0 < S)
    (hL : ∀ m γ, polynomialCoeffL1 (A m γ) ≤ M*D^m*S^(∑ i : Fin d, γ i))
    (z : Fin 3 ⊕ Fin d → ℂ)
    (hX : D*‖fun i : Fin 3 => z (.inl i)‖ ≤ 1/4)
    (hs : S*‖fun i : Fin d => z (.inr i)‖ ≤ 1/4)
    (α : Fin 3 ⊕ Fin d → ℕ) :
    ‖complexMultiindexDeriv (homogeneousSpectatorSum A) α z‖ ≤
      (2*(M*2^d))*(4*(3+(d:ℝ)))^(∑ i, α i)*
        (∏ i, ((α i).factorial : ℝ)) * ∏ i, ‖spectatorScalingCoefficient D S i‖^α i := by
  classical
  have hw := homogeneous_spectator_coordinate_word_factorial_bound A hA hM hD hS hL z hX hs
    (∑ i, α i) (multiindexCoordinateWord α)
  rw [multiindexCoordinateWord_prod α (fun i => ‖spectatorScalingCoefficient D S i‖)] at hw
  have hf := factorial_sum_le_card_pow_mul_prod_factorial_real α
  have hc : (Fintype.card (Fin 3 ⊕ Fin d) : ℝ) = 3+(d:ℝ) := by simp
  unfold complexMultiindexDeriv
  calc
    _ ≤ ((2*(M*2^d))*4^(∑ i, α i)*((∑ i, α i).factorial : ℝ))*
        ∏ i, ‖spectatorScalingCoefficient D S i‖^α i := hw
    _ ≤ ((2*(M*2^d))*4^(∑ i, α i)*
        ((Fintype.card (Fin 3 ⊕ Fin d) : ℝ)^(∑ i, α i)*∏ i, ((α i).factorial : ℝ)))*
        ∏ i, ‖spectatorScalingCoefficient D S i‖^α i := by
      apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg fun _ _ => pow_nonneg (norm_nonneg _) _)
      exact mul_le_mul_of_nonneg_left hf (by positivity)
    _ = (2*(M*2^d))*(4*(3+(d:ℝ)))^(∑ i, α i)*
        (∏ i, ((α i).factorial : ℝ)) * ∏ i, ‖spectatorScalingCoefficient D S i‖^α i := by
      rw [hc,mul_pow]
      ring

theorem homogeneous_spectator_mixed_multiindex_factorial_bound {d : ℕ}
    (A : ℕ → (Fin d → ℕ) → MvPolynomial (Fin 3) ℂ)
    (hA : ∀ m γ, (A m γ).IsHomogeneous m) {M D S : ℝ}
    (hM : 0 ≤ M) (hD : 0 < D) (hS : 0 < S)
    (hL : ∀ m γ, polynomialCoeffL1 (A m γ) ≤ M*D^m*S^(∑ i : Fin d, γ i))
    (z : Fin 3 ⊕ Fin d → ℂ)
    (hX : D*‖fun i : Fin 3 => z (.inl i)‖ ≤ 1/4)
    (hs : S*‖fun i : Fin d => z (.inr i)‖ ≤ 1/4)
    (α : Fin 3 → ℕ) (β : Fin d → ℕ) :
    ‖complexMultiindexDeriv (homogeneousSpectatorSum A) (Sum.elim α β) z‖ ≤
      (2*(M*2^d))*(4*(3+(d:ℝ))*D)^(∑ i, α i)*(4*(3+(d:ℝ))*S)^(∑ i, β i)*
        (∏ i, ((α i).factorial : ℝ))*(∏ i, ((β i).factorial : ℝ)) := by
  have h := homogeneous_spectator_multiindex_factorial_bound A hA hM hD hS hL z hX hs (Sum.elim α β)
  simp only [Fintype.sum_sum_type,Fintype.prod_sum_type,Sum.elim_inl,Sum.elim_inr,
    spectatorScalingCoefficient,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hD,abs_of_pos hS,Finset.prod_pow_eq_pow_sum] at h
  convert h using 1 <;> simp only [pow_add,mul_pow] <;> ring

end TheoremT.Continuum
