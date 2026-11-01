import GrushinFactorialIndexDecomposition_v1
import GrushinFactorialOuterL2_v1

/-! R13 row budgets from actual monomial-weighted L2 representatives at
lower-cost base indices. The input d is an indexed raw family: differential
identification remains explicit in applications. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace TheoremT.Continuum.WeakGrushin
set_option maxRecDepth 4096

abbrev FactorialRawJetFamily := (Fin 4 → ℕ) → (Fin 3 → ℕ) → Space (Fin 3) → ℂ

def FactorialShiftedOuterL2Rep {μ : Measure (Space (Fin 3))}
    (d : FactorialRawJetFamily)
    (W : (Fin 4 → ℕ) → (Fin 3 → ℕ) → FactorialOuterIndex → Lp ℂ 2 μ)
    (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) : Prop :=
  FactorialOuterL2Rep (fun η θ => d (α+η) (β+θ)) (W α β)

theorem factorial_multiindex_sub_add {ι : Type*} (α η : ι → ℕ)
    (h : ∀ i, η i ≤ α i) : (fun i => α i-η i)+η = α := by
  funext i
  exact Nat.sub_add_cancel (h i)

theorem factorial_zero_row_budget {μ : Measure (Space (Fin 3))}
    (d : FactorialRawJetFamily)
    (W : (Fin 4 → ℕ) → (Fin 3 → ℕ) → FactorialOuterIndex → Lp ℂ 2 μ)
    (r : ℕ) (N : ℝ) (hr : 2 ≤ r)
    (hW : ∀ a b, factorialMultiDerivativeCost a b ≤ r-2 → FactorialShiftedOuterL2Rep d W a b)
    (hN : ∀ a b, factorialMultiDerivativeCost a b ≤ r-2 → factorialOuterNorm (W a b) ≤ N)
    (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) (hc : factorialMultiDerivativeCost α β ≤ r) :
    ∃ w : Fin 4 → Lp ℂ 2 μ,
      (∀ l, w l =ᵐ[μ] (fun p => (p.1 l)^2 • d α β p)) ∧ (∑ l, ‖w l‖) ≤ N := by
  obtain ⟨η,θ,hη,hθ,hn,hcost⟩ := factorial_index_split_with_loss α β 2 r hr hc
  obtain ⟨w,hw,hwn⟩ := factorial_outer_square_row_L2 _ _ (hW _ _ hcost) η θ hn
  refine ⟨w,?_,hwn.trans (hN _ _ hcost)⟩
  simpa only [factorial_multiindex_sub_add α η hη,factorial_multiindex_sub_add β θ hθ] using hw

theorem factorial_first_y_row_budget {μ : Measure (Space (Fin 3))}
    (d : FactorialRawJetFamily)
    (W : (Fin 4 → ℕ) → (Fin 3 → ℕ) → FactorialOuterIndex → Lp ℂ 2 μ)
    (r : ℕ) (N : ℝ) (hr : 1 ≤ r)
    (hW : ∀ a b, factorialMultiDerivativeCost a b ≤ r-1 → FactorialShiftedOuterL2Rep d W a b)
    (hN : ∀ a b, factorialMultiDerivativeCost a b ≤ r-1 → factorialOuterNorm (W a b) ≤ N)
    (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) (hc : factorialMultiDerivativeCost α β ≤ r)
    (i : Fin 4) :
    ∃ w : Fin 4 → Lp ℂ 2 μ,
      (∀ l, w l =ᵐ[μ] (fun p => (p.1 l)^2 • d (α+Pi.single i 1) β p)) ∧
      (∑ l, ‖w l‖) ≤ N := by
  obtain ⟨η,θ,hη,hθ,hn,hcost⟩ := factorial_index_split_with_loss α β 1 r hr hc
  have houter : (∑ l, (η+Pi.single i 1 : Fin 4 → ℕ) l)+(∑ j, θ j) ≤ 2 := by
    simp only [Pi.add_apply,Finset.sum_add_distrib,Finset.sum_pi_single',Finset.mem_univ,ite_true]
    omega
  obtain ⟨w,hw,hwn⟩ := factorial_outer_square_row_L2 _ _ (hW _ _ hcost) (η+Pi.single i 1) θ houter
  refine ⟨w,?_,hwn.trans (hN _ _ hcost)⟩
  simpa only [← add_assoc,factorial_multiindex_sub_add α η hη,
    factorial_multiindex_sub_add β θ hθ] using hw

theorem factorial_first_t_row_budget {μ : Measure (Space (Fin 3))}
    (d : FactorialRawJetFamily)
    (W : (Fin 4 → ℕ) → (Fin 3 → ℕ) → FactorialOuterIndex → Lp ℂ 2 μ)
    (r : ℕ) (N : ℝ) (hr : 1 ≤ r)
    (hW : ∀ a b, factorialMultiDerivativeCost a b ≤ r-1 → FactorialShiftedOuterL2Rep d W a b)
    (hN : ∀ a b, factorialMultiDerivativeCost a b ≤ r-1 → factorialOuterNorm (W a b) ≤ N)
    (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) (hc : factorialMultiDerivativeCost α β ≤ r)
    (j : Fin 3) :
    ∃ w : Fin 4 → Lp ℂ 2 μ,
      (∀ l, w l =ᵐ[μ] (fun p => (p.1 l)^2 • d α (β+Pi.single j 1) p)) ∧
      (∑ l, ‖w l‖) ≤ N := by
  obtain ⟨η,θ,hη,hθ,hn,hcost⟩ := factorial_index_split_with_loss α β 1 r hr hc
  have houter : (∑ i, η i)+(∑ l, (θ+Pi.single j 1 : Fin 3 → ℕ) l) ≤ 2 := by
    simp only [Pi.add_apply,Finset.sum_add_distrib,Finset.sum_pi_single',Finset.mem_univ,ite_true]
    omega
  obtain ⟨w,hw,hwn⟩ := factorial_outer_square_row_L2 _ _ (hW _ _ hcost) η (θ+Pi.single j 1) houter
  refine ⟨w,?_,hwn.trans (hN _ _ hcost)⟩
  simpa only [← add_assoc,factorial_multiindex_sub_add α η hη,
    factorial_multiindex_sub_add β θ hθ] using hw

end TheoremT.Continuum.WeakGrushin
