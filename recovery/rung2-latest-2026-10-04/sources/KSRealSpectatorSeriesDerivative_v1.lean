import KSRealSpectatorSeriesData_v1
import HomogeneousSpectatorMultiindexDerivative_v1

/-! Explicit mixed derivative bounds for the actual A and B sums obtained
by finite KS descent of a prescribed polynomial/spectator family. The
coarse corrected rate is 4(3+d) times each respective coefficient rate,
on the quarter product polydisc. Physical Taylor inputs remain separate. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum
variable {d : ℕ}

theorem ks_real_spectator_series_mixed_factorial_bounds
    (P : ℕ → (Fin d → ℕ) → MvPolynomial (Fin 4) ℂ)
    (hP : ∀ m γ, (P m γ).IsHomogeneous (2*m))
    (hbal : ∀ m γ e, e ∈ (ksRealPolynomialToSpinor (P m γ)).support → e 0+e 1=e 2+e 3)
    {M b S : ℝ} (hM : 0 ≤ M) (hb : 0 < b) (hS : 0 < S)
    (hc : ∀ m γ e, e ∈ (P m γ).support →
      ‖(P m γ).coeff e‖ ≤ M*b^(2*m)*S^(∑ i : Fin d, γ i))
    (z : Fin 3 ⊕ Fin d → ℂ)
    (hX : (32*b^2)*‖fun i : Fin 3 => z (.inl i)‖ ≤ 1/4)
    (hs : S*‖fun i : Fin d => z (.inr i)‖ ≤ 1/4)
    (α : Fin 3 → ℕ) (β : Fin d → ℕ) :
    ‖complexMultiindexDeriv (homogeneousSpectatorSum (ksRealSpectatorFamilyA P)) (Sum.elim α β) z‖ ≤
      (2*(M*2^d))*(4*(3+(d:ℝ))*(32*b^2))^(∑ i, α i)*
        (4*(3+(d:ℝ))*S)^(∑ i, β i)*
        (∏ i, ((α i).factorial : ℝ))*(∏ i, ((β i).factorial : ℝ)) ∧
    ‖complexMultiindexDeriv (homogeneousSpectatorSum (ksRealSpectatorFamilyB P)) (Sum.elim α β) z‖ ≤
      (2*((M*(32*b^2))*2^d))*(4*(3+(d:ℝ))*(32*b^2))^(∑ i, α i)*
        (4*(3+(d:ℝ))*S)^(∑ i, β i)*
        (∏ i, ((α i).factorial : ℝ))*(∏ i, ((β i).factorial : ℝ)) := by
  obtain ⟨hA,hB,hB0,hLA,hLB⟩ := ks_real_spectator_series_data P hP hbal hM hb.le hS.le hc
  refine ⟨homogeneous_spectator_mixed_multiindex_factorial_bound _ hA hM (by positivity) hS hLA
    z hX hs α β, ?_⟩
  apply homogeneous_spectator_mixed_multiindex_factorial_bound _ hB
    (mul_nonneg hM (by positivity)) (by positivity) hS _ z hX hs α β
  intro n γ
  calc
    _ ≤ M*(32*b^2)^(n+1)*S^(∑ i : Fin d, γ i) := hLB n γ
    _ = (M*(32*b^2))*(32*b^2)^n*S^(∑ i : Fin d, γ i) := by rw [pow_succ]; ring

end TheoremT.Continuum
