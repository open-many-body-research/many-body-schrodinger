import GrushinFactorialPrincipalIndexedBound_v1

/-! Unweighted actual L2 components included in the full R3 norm.
The one-derivative extraction is the R17 lower-order estimate; unlike
an assumption of input L2 membership, its representative is constructed. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace TheoremT.Continuum.WeakGrushin
set_option maxRecDepth 4096

theorem factorial_unweighted_outer_mem (η : Fin 4 → ℕ) (θ : Fin 3 → ℕ)
    (h : (∑ i, η i)+(∑ j, θ j) ≤ 1) :
    (η,θ,0) ∈ factorialOuterIndices := by
  rw [factorialOuterIndices_mem]
  simp only [factorialOuterAdmissible,Pi.zero_apply,Finset.sum_const_zero]
  omega

theorem factorial_shifted_unweighted_outer_L2 {μ : Measure (Space (Fin 3))}
    (d : FactorialRawJetFamily)
    (W : (Fin 4 → ℕ) → (Fin 3 → ℕ) → FactorialOuterIndex → Lp ℂ 2 μ)
    (a : Fin 4 → ℕ) (b : Fin 3 → ℕ) (hW : FactorialShiftedOuterL2Rep d W a b)
    (η : Fin 4 → ℕ) (θ : Fin 3 → ℕ) (h : (∑ i, η i)+(∑ j, θ j) ≤ 1) :
    ∃ U : Lp ℂ 2 μ, U =ᵐ[μ] d (a+η) (b+θ) ∧ ‖U‖ ≤ factorialOuterNorm (W a b) := by
  have hm := factorial_unweighted_outer_mem η θ h
  refine ⟨W a b (η,θ,0),?_,factorialOuterIndex_norm_le _ _ hm⟩
  have hrep := hW (η,θ,0) hm
  simpa only [factorialYMonomial_zero,one_smul] using hrep

theorem factorial_unweighted_component_L2 {μ : Measure (Space (Fin 3))}
    (d : FactorialRawJetFamily)
    (W : (Fin 4 → ℕ) → (Fin 3 → ℕ) → FactorialOuterIndex → Lp ℂ 2 μ)
    (r : ℕ) (N : ℝ)
    (hW : ∀ a b, factorialMultiDerivativeCost a b ≤ r → FactorialShiftedOuterL2Rep d W a b)
    (hN : ∀ a b, factorialMultiDerivativeCost a b ≤ r → factorialOuterNorm (W a b) ≤ N)
    (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) (hc : factorialMultiDerivativeCost α β ≤ r) :
    ∃ U : Lp ℂ 2 μ, U =ᵐ[μ] d α β ∧ ‖U‖ ≤ N := by
  obtain ⟨U,hU,hUn⟩ := factorial_shifted_unweighted_outer_L2 d W α β (hW α β hc) 0 0 (by simp)
  exact ⟨U,by simpa only [add_zero] using hU,hUn.trans (hN α β hc)⟩

theorem factorial_unweighted_lower_order_L2 {μ : Measure (Space (Fin 3))}
    (d : FactorialRawJetFamily)
    (W : (Fin 4 → ℕ) → (Fin 3 → ℕ) → FactorialOuterIndex → Lp ℂ 2 μ)
    (r : ℕ) (N : ℝ) (hr : 1 ≤ r)
    (hW : ∀ a b, factorialMultiDerivativeCost a b ≤ r-1 → FactorialShiftedOuterL2Rep d W a b)
    (hN : ∀ a b, factorialMultiDerivativeCost a b ≤ r-1 → factorialOuterNorm (W a b) ≤ N)
    (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) (hc : factorialMultiDerivativeCost α β ≤ r) :
    ∃ U : Lp ℂ 2 μ, U =ᵐ[μ] d α β ∧ ‖U‖ ≤ N := by
  obtain ⟨η,θ,hη,hθ,hn,hcost⟩ := factorial_index_split_with_loss α β 1 r hr hc
  obtain ⟨U,hU,hUn⟩ := factorial_shifted_unweighted_outer_L2 d W _ _ (hW _ _ hcost) η θ hn
  refine ⟨U,?_,hUn.trans (hN _ _ hcost)⟩
  simpa only [factorial_multiindex_sub_add α η hη,factorial_multiindex_sub_add β θ hθ] using hU

end TheoremT.Continuum.WeakGrushin
