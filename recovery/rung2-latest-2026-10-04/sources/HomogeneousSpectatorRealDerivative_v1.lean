import HomogeneousSpectatorMultiindexDerivative_v1
import HomogeneousSpectatorAnisotropicAnalytic_v1
import RealRestrictionIteratedDerivativeWord_v1

/-! Transfer the explicit mixed derivative estimate to actual real
coordinates. The real derivative is the literal real iterated Frechet
derivative, evaluated on the same finite multiindex word. Equality with
the complex derivative is proved from scalar restriction and the actual
coordinate embedding. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum

def realMultiindexDeriv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → ℝ) → ℂ) (α : ι → ℕ) (z : ι → ℝ) : ℂ :=
  iteratedFDeriv ℝ (∑ i, α i) f z
    (fun j => Pi.single (multiindexCoordinateWord α j) (1 : ℝ))

theorem realMultiindexDeriv_restriction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → ℂ) → ℂ) (α : ι → ℕ) (z : ι → ℝ)
    (hf : ContDiffAt ℂ (∑ i, α i : ℕ) f (fun i => (z i : ℂ))) :
    realMultiindexDeriv (fun x : ι → ℝ => f (fun i => (x i : ℂ))) α z =
      complexMultiindexDeriv f α (fun i => (z i : ℂ)) :=
  real_restriction_iteratedFDeriv_word f z (∑ i, α i) (multiindexCoordinateWord α) hf

theorem finite_real_complexification_norm {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    ‖fun i => (x i : ℂ)‖ = ‖x‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
    intro i
    simpa only [Complex.norm_real] using norm_le_pi_norm x i
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (fun i => (x i : ℂ)))).mpr
    intro i
    simpa only [Complex.norm_real] using norm_le_pi_norm (fun i => (x i : ℂ)) i

theorem homogeneous_spectator_real_mixed_multiindex_factorial_bound {d : ℕ}
    (A : ℕ → (Fin d → ℕ) → MvPolynomial (Fin 3) ℂ)
    (hA : ∀ m γ, (A m γ).IsHomogeneous m) {M D S : ℝ}
    (hM : 0 ≤ M) (hD : 0 < D) (hS : 0 < S)
    (hL : ∀ m γ, polynomialCoeffL1 (A m γ) ≤ M*D^m*S^(∑ i : Fin d, γ i))
    (z : Fin 3 ⊕ Fin d → ℝ)
    (hX : D*‖fun i : Fin 3 => z (.inl i)‖ ≤ 1/4)
    (hs : S*‖fun i : Fin d => z (.inr i)‖ ≤ 1/4)
    (α : Fin 3 → ℕ) (β : Fin d → ℕ) :
    ‖realMultiindexDeriv
      (fun x : Fin 3 ⊕ Fin d → ℝ => homogeneousSpectatorSum A (fun i => (x i : ℂ)))
      (Sum.elim α β) z‖ ≤
      (2*(M*2^d))*(4*(3+(d:ℝ))*D)^(∑ i, α i)*(4*(3+(d:ℝ))*S)^(∑ i, β i)*
        (∏ i, ((α i).factorial : ℝ))*(∏ i, ((β i).factorial : ℝ)) := by
  have hXc : D*‖fun i : Fin 3 => (z (.inl i) : ℂ)‖ ≤ 1/4 := by
    simpa only [finite_real_complexification_norm] using hX
  have hsc : S*‖fun i : Fin d => (z (.inr i) : ℂ)‖ ≤ 1/4 := by
    simpa only [finite_real_complexification_norm] using hs
  have hana : AnalyticAt ℂ (homogeneousSpectatorSum A) (fun i => (z i : ℂ)) :=
    homogeneous_spectator_sum_analytic_anisotropic A hA hM hD.le hS.le hL _
      ⟨by change D*‖fun i : Fin 3 => (z (.inl i) : ℂ)‖ < 1; linarith,
       by change S*‖fun i : Fin d => (z (.inr i) : ℂ)‖ < 1; linarith⟩
  rw [realMultiindexDeriv_restriction _ _ _ hana.contDiffAt]
  exact homogeneous_spectator_mixed_multiindex_factorial_bound A hA hM hD hS hL _ hXc hsc α β

end TheoremT.Continuum
