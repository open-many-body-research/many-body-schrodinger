import GrushinFactorialPrincipalIndexSplit_v1
import GrushinFactorialIndexRowBudget_v1

/-! Actual L2 representatives for each one-hit and two-hit principal
coefficient component, using exact R14 decompositions and the full M norm. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace TheoremT.Continuum.WeakGrushin
set_option maxRecDepth 4096

theorem factorialOuterIndex_norm_le {E : Type*} [SeminormedAddCommGroup E]
    (F : FactorialOuterIndex → E) (m : FactorialOuterIndex)
    (hm : m ∈ factorialOuterIndices) : ‖F m‖ ≤ factorialOuterNorm F :=
  Finset.single_le_sum (fun x _ => norm_nonneg _) hm

theorem factorialYMonomial_single (i : Fin 4) (y : EuclideanSpace ℝ (Fin 4)) :
    factorialYMonomial (Pi.single i 1) y = y i := by
  classical
  unfold factorialYMonomial
  rw [Finset.prod_eq_single i]
  · simp
  · intro j hj hji
    simp [hji]
  · simp

theorem factorial_principal_one_hit_component_L2 {μ : Measure (Space (Fin 3))}
    (d : FactorialRawJetFamily)
    (W : (Fin 4 → ℕ) → (Fin 3 → ℕ) → FactorialOuterIndex → Lp ℂ 2 μ)
    (r : ℕ) (N : ℝ)
    (hW : ∀ a b, factorialMultiDerivativeCost a b ≤ r-1 → FactorialShiftedOuterL2Rep d W a b)
    (hN : ∀ a b, factorialMultiDerivativeCost a b ≤ r-1 → factorialOuterNorm (W a b) ≤ N)
    (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) (hc : factorialMultiDerivativeCost α β ≤ r)
    (i : Fin 4) (j : Fin 3) (hi : 1 ≤ α i) :
    ∃ U : Lp ℂ 2 μ,
      U =ᵐ[μ] (fun p => p.1 i •
        d (fun l => α l-(Pi.single i 1 : Fin 4 → ℕ) l) (β+Pi.single j 2) p) ∧ ‖U‖ ≤ N := by
  obtain ⟨a,η,heq,hm,hcost⟩ := factorial_principal_one_hit_split α β i j hi
  have hbase : factorialMultiDerivativeCost a (β+Pi.single j 1) ≤ r-1 := by omega
  let m : FactorialOuterIndex := (η,Pi.single j 1,Pi.single i 1)
  refine ⟨W a (β+Pi.single j 1) m,?_,
    (factorialOuterIndex_norm_le _ m hm).trans (hN _ _ hbase)⟩
  have hrep := hW a (β+Pi.single j 1) hbase m hm
  simpa only [m,factorialYMonomial_single,heq,factorial_multiindex_double_single] using hrep

theorem factorial_principal_two_hit_component_L2 {μ : Measure (Space (Fin 3))}
    (d : FactorialRawJetFamily)
    (W : (Fin 4 → ℕ) → (Fin 3 → ℕ) → FactorialOuterIndex → Lp ℂ 2 μ)
    (r : ℕ) (N : ℝ)
    (hW : ∀ a b, factorialMultiDerivativeCost a b ≤ r-2 → FactorialShiftedOuterL2Rep d W a b)
    (hN : ∀ a b, factorialMultiDerivativeCost a b ≤ r-2 → factorialOuterNorm (W a b) ≤ N)
    (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) (hc : factorialMultiDerivativeCost α β ≤ r)
    (i : Fin 4) (j : Fin 3) (hi : 2 ≤ α i) :
    ∃ U : Lp ℂ 2 μ,
      U =ᵐ[μ] d (fun l => α l-(Pi.single i 2 : Fin 4 → ℕ) l) (β+Pi.single j 2) ∧ ‖U‖ ≤ N := by
  obtain ⟨a,b,η,θ,heqY,heqT,hm,hcost⟩ := factorial_principal_two_hit_split α β i j hi
  have hbase : factorialMultiDerivativeCost a b ≤ r-2 := by omega
  let m : FactorialOuterIndex := (η,θ,0)
  refine ⟨W a b m,?_,(factorialOuterIndex_norm_le _ m hm).trans (hN _ _ hbase)⟩
  have hrep := hW a b hbase m hm
  simpa only [m,factorialYMonomial_zero,one_smul,heqY,heqT] using hrep

end TheoremT.Continuum.WeakGrushin
