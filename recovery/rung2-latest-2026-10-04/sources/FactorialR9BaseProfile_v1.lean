import FactorialProfileFiniteBudgetBound_v1
import ProductMixedFiniteBudgetTransfer_v1
import GrushinFactorialLocalRepresentatives_v1

/-! R9 base profiles from an actual finite weak H12 budget. One separately
selected genuine raw derivative family is fixed before every base order and
subregion. Local weak uniqueness transfers the original budget to that
family; actual weighted L2 representatives and their bounds are conclusions. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
set_option maxRecDepth 4096
namespace TheoremT.Continuum.WeakGrushin

theorem factorial_profile_bound_of_weak_finite_budget
    {Ω : Set (Space (Fin 3))} (hΩ : IsOpen Ω)
    {f : Space (Fin 3) → ℂ} {m : ℕ} {W S : ℝ}
    (hf : ProductMixedMultiIndexWeakHk Ω f m W)
    (F : FactorialRawJetFamily)
    (hF0 : ∀ᵐ p ∂volume, p ∈ Ω → F 0 0 p = f p)
    (hFY : ∀ a b i, (∑ k,a k)+(∑ j,b j) < m →
      ProductLocalWeakDirectional Ω (F a b) (F (a+Pi.single i 1) b) (yDir i))
    (hFT : ∀ a b j, (∑ i,a i)+(∑ k,b k) < m →
      ProductLocalWeakDirectional Ω (F a b) (F a (b+Pi.single j 1)) (tDir j))
    (hS : 1 ≤ S) (hΩS : ∀ p ∈ Ω, ‖p.1‖ ≤ S)
    {r : ℕ} (hr : r+2 ≤ m) {O : Set (Space (Fin 3))} (hO : O ⊆ Ω) :
    FactorialLocalMemLp F O r ∧ factorialLocalProfile F O r ≤ 498*S^2*Real.sqrt W := by
  exact factorial_profile_bound_on_subregion_of_budgets hΩ.measurableSet hS hΩS F hr
    (product_mixed_finite_budget_transfer_of_local_ae hΩ hf F hF0 hFY hFT) hO

theorem factorial_R9_base_profile_of_H12
    {Ω : Set (Space (Fin 3))} (hΩ : IsOpen Ω)
    {f : Space (Fin 3) → ℂ} {W S : ℝ}
    (hf : ProductMixedMultiIndexWeakHk Ω f 12 W)
    (F : FactorialRawJetFamily)
    (hF0 : ∀ᵐ p ∂volume, p ∈ Ω → F 0 0 p = f p)
    (hFY : ∀ a b i, (∑ k,a k)+(∑ j,b j) < 12 →
      ProductLocalWeakDirectional Ω (F a b) (F (a+Pi.single i 1) b) (yDir i))
    (hFT : ∀ a b j, (∑ i,a i)+(∑ k,b k) < 12 →
      ProductLocalWeakDirectional Ω (F a b) (F a (b+Pi.single j 1)) (tDir j))
    (hS : 1 ≤ S) (hΩS : ∀ p ∈ Ω, ‖p.1‖ ≤ S) :
    ∀ r : ℕ, r ≤ 8 → ∀ O : Set (Space (Fin 3)), O ⊆ Ω →
      FactorialLocalMemLp F O r ∧
      factorialLocalProfile F O r ≤ 498*S^2*Real.sqrt W ∧
      ∃ V : (Fin 4 → ℕ) → (Fin 3 → ℕ) → FactorialOuterIndex → Lp ℂ 2 (volume.restrict O),
        ∀ a b, factorialMultiDerivativeCost a b ≤ r →
          FactorialShiftedOuterL2Rep F V a b ∧
          factorialOuterNorm (V a b) = factorialLocalOuterNorm F O a b ∧
          factorialOuterNorm (V a b) ≤ 498*S^2*Real.sqrt W := by
  intro r hr O hO
  obtain ⟨hfin,hbound⟩ := factorial_profile_bound_of_weak_finite_budget hΩ hf F hF0 hFY hFT
    hS hΩS (by omega : r+2 ≤ 12) hO
  obtain ⟨V,hV⟩ := factorialLocalProfile_representatives hfin
  refine ⟨hfin,hbound,V,?_⟩
  intro a b hab
  exact ⟨(hV a b hab).1,(hV a b hab).2.1,(hV a b hab).2.2.trans hbound⟩

end TheoremT.Continuum.WeakGrushin
