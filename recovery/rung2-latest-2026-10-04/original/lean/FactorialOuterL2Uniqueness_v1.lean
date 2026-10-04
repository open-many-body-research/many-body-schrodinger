import GrushinFactorialOuterL2_v1

/-! The fixed finite outer norm does not depend on the representatives
chosen for the actual derivative fields. Only the indices in the prescribed
outer set contribute; values outside it remain irrelevant. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
set_option maxRecDepth 4096
namespace TheoremT.Continuum.WeakGrushin

theorem FactorialOuterL2Rep.congr_ae {μ : Measure (Space (Fin 3))}
    {D F : (Fin 4 → ℕ) → (Fin 3 → ℕ) → Space (Fin 3) → ℂ}
    {W : FactorialOuterIndex → Lp ℂ 2 μ} (hW : FactorialOuterL2Rep D W)
    (hDF : ∀ α β, (∑ i, α i)+(∑ j, β j) ≤ 2 → D α β =ᵐ[μ] F α β) :
    FactorialOuterL2Rep F W := by
  intro m hm
  apply (hW m hm).trans
  filter_upwards [hDF m.1 m.2.1 (((factorialOuterIndices_mem m).mp hm).1)] with p hp
  rw [hp]

theorem FactorialOuterL2Rep.unique_on_indices {μ : Measure (Space (Fin 3))}
    {D : (Fin 4 → ℕ) → (Fin 3 → ℕ) → Space (Fin 3) → ℂ}
    {W V : FactorialOuterIndex → Lp ℂ 2 μ}
    (hW : FactorialOuterL2Rep D W) (hV : FactorialOuterL2Rep D V) :
    ∀ m ∈ factorialOuterIndices, W m = V m := by
  intro m hm
  exact Lp.ext ((hW m hm).trans (hV m hm).symm)

theorem FactorialOuterL2Rep.norm_eq {μ : Measure (Space (Fin 3))}
    {D : (Fin 4 → ℕ) → (Fin 3 → ℕ) → Space (Fin 3) → ℂ}
    {W V : FactorialOuterIndex → Lp ℂ 2 μ}
    (hW : FactorialOuterL2Rep D W) (hV : FactorialOuterL2Rep D V) :
    factorialOuterNorm W = factorialOuterNorm V := by
  apply Finset.sum_congr rfl
  intro m hm
  rw [hW.unique_on_indices hV m hm]

theorem FactorialOuterL2Rep.norm_eq_of_ae {μ : Measure (Space (Fin 3))}
    {D F : (Fin 4 → ℕ) → (Fin 3 → ℕ) → Space (Fin 3) → ℂ}
    {W V : FactorialOuterIndex → Lp ℂ 2 μ}
    (hW : FactorialOuterL2Rep D W) (hV : FactorialOuterL2Rep F V)
    (hDF : ∀ α β, (∑ i, α i)+(∑ j, β j) ≤ 2 → D α β =ᵐ[μ] F α β) :
    factorialOuterNorm W = factorialOuterNorm V :=
  (hW.congr_ae hDF).norm_eq hV

end TheoremT.Continuum.WeakGrushin
