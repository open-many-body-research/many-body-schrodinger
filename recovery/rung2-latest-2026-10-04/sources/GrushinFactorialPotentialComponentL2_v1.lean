import GrushinFactorialUnweightedComponent_v1

/-! Actual bounded-potential Leibniz components for R16. The removed
multiindex has its exact total degree, which reduces the R6 cost before
constructing the L2 input and applying the bounded real multiplier. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace TheoremT.Continuum.WeakGrushin
set_option maxRecDepth 4096

theorem factorial_potential_leibniz_component_L2
    {μ : Measure (Space (Fin 3))} (d : FactorialRawJetFamily)
    (W : (Fin 4 → ℕ) → (Fin 3 → ℕ) → FactorialOuterIndex → Lp ℂ 2 μ)
    (r j : ℕ) (N : ℝ)
    (hW : ∀ a b, factorialMultiDerivativeCost a b ≤ r-j → FactorialShiftedOuterL2Rep d W a b)
    (hN : ∀ a b, factorialMultiDerivativeCost a b ≤ r-j → factorialOuterNorm (W a b) ≤ N)
    (α η : Fin 4 → ℕ) (β θ : Fin 3 → ℕ)
    (hc : factorialMultiDerivativeCost α β ≤ r)
    (hη : ∀ i, η i ≤ α i) (hθ : ∀ l, θ l ≤ β l)
    (hj : (∑ i, η i)+(∑ l, θ l) = j)
    (q : Space (Fin 3) → ℝ) (hq : AEStronglyMeasurable q μ)
    (K : ℝ) (hK : 0 ≤ K) (hqK : ∀ᵐ p ∂μ, |q p| ≤ K) :
    ∃ H : Lp ℂ 2 μ,
      H =ᵐ[μ] (fun p => q p • d (fun i => α i-η i) (fun l => β l-θ l) p) ∧
      ‖H‖ ≤ K*N := by
  have hrem := factorialMultiDerivativeCost_remove α η β θ hη hθ
  rw [hj] at hrem
  have hcost : factorialMultiDerivativeCost (fun i => α i-η i) (fun l => β l-θ l) ≤ r-j := by omega
  obtain ⟨U,hU,hUn⟩ := factorial_unweighted_component_L2 d W (r-j) N hW hN _ _ hcost
  have hqn : ∀ᵐ p ∂μ, ‖q p‖ ≤ K := by simpa only [Real.norm_eq_abs] using hqK
  have htop : MemLp q ⊤ μ := memLp_top_of_bound hq K hqn
  refine ⟨measureBoundedRealMul q htop U,?_,
    (measureBoundedRealMul_norm_le q htop hqn U).trans (mul_le_mul_of_nonneg_left hUn hK)⟩
  filter_upwards [measureBoundedRealMul_ae q htop U,hU] with p hp hu
  rw [hp,hu]

end TheoremT.Continuum.WeakGrushin
