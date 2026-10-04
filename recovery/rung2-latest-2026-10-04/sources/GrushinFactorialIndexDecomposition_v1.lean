import GrushinFactorialOuterIndex_v1
import Mathlib.Data.Finsupp.Weight

/-! Concrete componentwise index splittings for R13/R14. The chosen
removed multiindex is proved to exist; it is not a supplied assumption. -/
noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum.WeakGrushin
set_option maxRecDepth 4096

theorem finite_submultiindex_degree {ι : Type*} [Fintype ι]
    (α : ι → ℕ) (n : ℕ) (h : n ≤ ∑ i, α i) :
    ∃ η : ι → ℕ, (∀ i, η i ≤ α i) ∧ (∑ i, η i) = n := by
  let f : ι →₀ ℕ := Finsupp.equivFunOnFinite.symm α
  have hf : f.degree = ∑ i, α i := by
    rw [Finsupp.degree_eq_sum]
    rfl
  obtain ⟨g,hg,hdeg⟩ := Finsupp.exists_le_degree_eq f n (by rwa [hf])
  refine ⟨g,fun i => hg i,?_⟩
  simpa only [Finsupp.degree_eq_sum] using hdeg

theorem factorial_submultiindex_degree
    (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) (n : ℕ)
    (h : n ≤ (∑ i, α i)+(∑ j, β j)) :
    ∃ η : Fin 4 → ℕ, ∃ θ : Fin 3 → ℕ,
      (∀ i, η i ≤ α i) ∧ (∀ j, θ j ≤ β j) ∧
      (∑ i, η i)+(∑ j, θ j) = n := by
  have hs : n ≤ ∑ k : Fin 4 ⊕ Fin 3, Sum.elim α β k := by
    simpa only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr] using h
  obtain ⟨q,hq,hqn⟩ := finite_submultiindex_degree (Sum.elim α β) n hs
  exact ⟨(fun i => q (.inl i)),(fun j => q (.inr j)),
    (fun i => hq (.inl i)),(fun j => hq (.inr j)),
    by simpa only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr] using hqn⟩

theorem factorial_index_split_with_loss
    (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) (k r : ℕ)
    (hkr : k ≤ r) (hcost : factorialMultiDerivativeCost α β ≤ r) :
    ∃ η : Fin 4 → ℕ, ∃ θ : Fin 3 → ℕ,
      (∀ i, η i ≤ α i) ∧ (∀ j, θ j ≤ β j) ∧
      (∑ i, η i)+(∑ j, θ j) ≤ k ∧
      factorialMultiDerivativeCost (fun i => α i-η i) (fun j => β j-θ j) ≤ r-k := by
  by_cases ht : (∑ i, α i)+(∑ j, β j) ≤ k
  · refine ⟨α,β,(fun i => le_rfl),(fun j => le_rfl),ht,?_⟩
    simp [factorialMultiDerivativeCost,factorialDerivativeCost]
  · obtain ⟨η,θ,hη,hθ,hn⟩ := factorial_submultiindex_degree α β k (by omega)
    refine ⟨η,θ,hη,hθ,hn.le,?_⟩
    have hrem := factorialMultiDerivativeCost_remove α η β θ hη hθ
    rw [hn] at hrem
    omega

theorem factorial_second_cutoff_outer_split
    (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) (r : ℕ)
    (hr : 2 ≤ r) (hc : factorialMultiDerivativeCost α β ≤ r) :
    ∃ η : Fin 4 → ℕ, ∃ θ : Fin 3 → ℕ,
      (∀ i, η i ≤ α i) ∧ (∀ j, θ j ≤ β j) ∧
      (∀ l, factorialSquareOuterIndex η θ l ∈ factorialOuterIndices) ∧
      factorialMultiDerivativeCost (fun i => α i-η i) (fun j => β j-θ j) ≤ r-2 := by
  obtain ⟨η,θ,hη,hθ,hn,hcost⟩ := factorial_index_split_with_loss α β 2 r hr hc
  exact ⟨η,θ,hη,hθ,(fun l => factorialSquareOuterIndex_mem η θ hn l),hcost⟩

theorem factorial_first_cutoff_y_outer_split
    (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) (r : ℕ) (i : Fin 4)
    (hr : 1 ≤ r) (hc : factorialMultiDerivativeCost α β ≤ r) :
    ∃ η : Fin 4 → ℕ, ∃ θ : Fin 3 → ℕ,
      (∀ l, η l ≤ α l) ∧ (∀ j, θ j ≤ β j) ∧
      (∀ l, factorialSquareOuterIndex (η+Pi.single i 1) θ l ∈ factorialOuterIndices) ∧
      factorialMultiDerivativeCost (fun l => α l-η l) (fun j => β j-θ j) ≤ r-1 := by
  obtain ⟨η,θ,hη,hθ,hn,hcost⟩ := factorial_index_split_with_loss α β 1 r hr hc
  refine ⟨η,θ,hη,hθ,?_,hcost⟩
  intro l
  apply factorialSquareOuterIndex_mem
  simp only [Pi.add_apply,Finset.sum_add_distrib,Finset.sum_pi_single',Finset.mem_univ,ite_true]
  omega

theorem factorial_first_cutoff_t_outer_split
    (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) (r : ℕ) (j : Fin 3)
    (hr : 1 ≤ r) (hc : factorialMultiDerivativeCost α β ≤ r) :
    ∃ η : Fin 4 → ℕ, ∃ θ : Fin 3 → ℕ,
      (∀ i, η i ≤ α i) ∧ (∀ l, θ l ≤ β l) ∧
      (∀ l, factorialSquareOuterIndex η (θ+Pi.single j 1) l ∈ factorialOuterIndices) ∧
      factorialMultiDerivativeCost (fun i => α i-η i) (fun l => β l-θ l) ≤ r-1 := by
  obtain ⟨η,θ,hη,hθ,hn,hcost⟩ := factorial_index_split_with_loss α β 1 r hr hc
  refine ⟨η,θ,hη,hθ,?_,hcost⟩
  intro l
  apply factorialSquareOuterIndex_mem
  simp only [Pi.add_apply,Finset.sum_add_distrib,Finset.sum_pi_single',Finset.mem_univ,ite_true]
  omega

end TheoremT.Continuum.WeakGrushin
