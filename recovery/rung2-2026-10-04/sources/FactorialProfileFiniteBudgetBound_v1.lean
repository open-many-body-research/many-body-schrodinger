import FactorialMonomialBudgetBound_v1
import GrushinFactorialLocalProfile_v1
import GrushinFactorialOuterCardinality_v1

/-! A true finite local profile bound from ordinary finite derivative
budgets. The exact derivative-cost definition controls shifted total order,
and every weighted component is proved to have finite L2 norm before the
finite maximum is bounded. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
set_option maxRecDepth 4096
namespace TheoremT.Continuum.WeakGrushin

theorem factorial_shifted_total_le_of_cost
    (a : Fin 4 → ℕ) (b : Fin 3 → ℕ) {r : ℕ}
    (hab : factorialMultiDerivativeCost a b ≤ r)
    {m : FactorialOuterIndex} (hm : m ∈ factorialOuterIndices) :
    (∑ i, (a+m.1) i)+(∑ j, (b+m.2.1) j) ≤ r+2 := by
  have ht := factorialDerivativeCost_total_le (∑ i,a i) (∑ j,b j)
  change (∑ i,a i)+(∑ j,b j) ≤ factorialMultiDerivativeCost a b at ht
  have ho := ((factorialOuterIndices_mem m).mp hm).1
  simp only [Pi.add_apply,Finset.sum_add_distrib]
  omega

theorem factorial_profile_bound_of_region_budgets
    {Ω : Set (Space (Fin 3))} (hΩ : MeasurableSet Ω)
    {S W : ℝ} (hS : 1 ≤ S) (hΩS : ∀ p ∈ Ω, ‖p.1‖ ≤ S)
    (D : FactorialRawJetFamily) {m r : ℕ} (hrm : r+2 ≤ m)
    (hD : ∀ a b, (∑ i,a i)+(∑ j,b j) ≤ m → RegionL2Budget (D a b) Ω W) :
    FactorialLocalMemLp D Ω r ∧
    (∀ a b, factorialMultiDerivativeCost a b ≤ r →
      factorialLocalOuterNorm D Ω a b ≤ 498*S^2*Real.sqrt W) ∧
    factorialLocalProfile D Ω r ≤ 498*S^2*Real.sqrt W := by
  have hcomp (a : Fin 4 → ℕ) (b : Fin 3 → ℕ)
      (hab : factorialMultiDerivativeCost a b ≤ r)
      (q : FactorialOuterIndex) (hq : q ∈ factorialOuterIndices) :
      MemLp (factorialShiftedWeightedField D a b q) 2 (volume.restrict Ω) ∧
      (eLpNorm (factorialShiftedWeightedField D a b q) 2 (volume.restrict Ω)).toReal ≤
        S^2*Real.sqrt W := by
    have hd := hD (a+q.1) (b+q.2.1) ((factorial_shifted_total_le_of_cost a b hab hq).trans hrm)
    have hh := factorial_monomial_region_budget_bound hΩ hS hΩS hd q.2.2
      (((factorialOuterIndices_mem q).mp hq).2.1)
    exact ⟨hh.1,hh.2.1⟩
  have hout (a : Fin 4 → ℕ) (b : Fin 3 → ℕ)
      (hab : factorialMultiDerivativeCost a b ≤ r) :
      factorialLocalOuterNorm D Ω a b ≤ 498*S^2*Real.sqrt W := by
    calc
      factorialLocalOuterNorm D Ω a b ≤ ∑ q ∈ factorialOuterIndices, S^2*Real.sqrt W :=
        Finset.sum_le_sum (fun q hq => (hcomp a b hab q hq).2)
      _ = _ := by simp [factorialOuterIndices_card,mul_assoc]
  refine ⟨fun a b hab q hq => (hcomp a b hab q hq).1,hout,?_⟩
  apply Finset.sup'_le
  intro q hq
  exact hout q.1 q.2 ((factorialBaseIndices_mem r q).mp hq)

theorem factorial_profile_bound_on_subregion_of_budgets
    {Ω : Set (Space (Fin 3))} (hΩ : MeasurableSet Ω)
    {S W : ℝ} (hS : 1 ≤ S) (hΩS : ∀ p ∈ Ω, ‖p.1‖ ≤ S)
    (D : FactorialRawJetFamily) {m r : ℕ} (hrm : r+2 ≤ m)
    (hD : ∀ a b, (∑ i,a i)+(∑ j,b j) ≤ m → RegionL2Budget (D a b) Ω W)
    {O : Set (Space (Fin 3))} (hO : O ⊆ Ω) :
    FactorialLocalMemLp D O r ∧ factorialLocalProfile D O r ≤ 498*S^2*Real.sqrt W := by
  obtain ⟨hf,_,hb⟩ := factorial_profile_bound_of_region_budgets hΩ hS hΩS D hrm hD
  exact ⟨hf.restrict hO,(factorialLocalProfile_mono_domain hf hO).trans hb⟩

end TheoremT.Continuum.WeakGrushin
