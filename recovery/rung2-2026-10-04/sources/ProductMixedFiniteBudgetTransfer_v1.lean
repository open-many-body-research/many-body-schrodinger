import ProductMixedMultiIndexWeakHk_v1
import ProductWeakFiniteFamilyUnique_v1

/-! Transfer of an already established finite Sobolev budget to a separately
chosen genuine multiindex derivative family of the same raw function. Local
weak uniqueness supplies equality on the open region; the existing budget is
then transported almost everywhere. No second norm budget is assumed. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace TheoremT.Continuum.WeakGrushin

theorem product_mixed_finite_budget_transfer_of_local_ae
    {Ω : Set (Space (Fin 3))} (hΩ : IsOpen Ω)
    {f : Space (Fin 3) → ℂ} {m : ℕ} {W : ℝ}
    (hf : ProductMixedMultiIndexWeakHk Ω f m W)
    (F : (Fin 4 → ℕ) → (Fin 3 → ℕ) → Space (Fin 3) → ℂ)
    (hF0 : ∀ᵐ p ∂volume, p ∈ Ω → F 0 0 p = f p)
    (hFY : ∀ α β i, (∑ k, α k)+(∑ j, β j) < m →
      ProductLocalWeakDirectional Ω (F α β) (F (α+Pi.single i 1) β) (yDir i))
    (hFT : ∀ α β j, (∑ i, α i)+(∑ k, β k) < m →
      ProductLocalWeakDirectional Ω (F α β) (F α (β+Pi.single j 1)) (tDir j))
    (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) (hab : (∑ i, α i)+(∑ j, β j) ≤ m) :
    RegionL2Budget (F α β) Ω W := by
  obtain ⟨G, hG0, hBudget, hGY, hGT⟩ := hf
  have h0 : ∀ᵐ p ∂volume, p ∈ Ω → G 0 0 p = F 0 0 p := by
    filter_upwards [hF0] with p hp hin
    rw [hG0]
    exact (hp hin).symm
  have heq := product_mixed_multiIndex_weak_families_unique hΩ G F h0
    hGY hGT hFY hFT α β hab
  exact (hBudget α β hab).congr_ae ((ae_restrict_iff' hΩ.measurableSet).mpr heq)

theorem product_mixed_finite_budget_transfer
    {Ω : Set (Space (Fin 3))} (hΩ : IsOpen Ω)
    {f : Space (Fin 3) → ℂ} {m : ℕ} {W : ℝ}
    (hf : ProductMixedMultiIndexWeakHk Ω f m W)
    (F : (Fin 4 → ℕ) → (Fin 3 → ℕ) → Space (Fin 3) → ℂ)
    (hF0 : F 0 0 = f)
    (hFY : ∀ α β i, (∑ k, α k)+(∑ j, β j) < m →
      ProductLocalWeakDirectional Ω (F α β) (F (α+Pi.single i 1) β) (yDir i))
    (hFT : ∀ α β j, (∑ i, α i)+(∑ k, β k) < m →
      ProductLocalWeakDirectional Ω (F α β) (F α (β+Pi.single j 1)) (tDir j))
    (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) (hab : (∑ i, α i)+(∑ j, β j) ≤ m) :
    RegionL2Budget (F α β) Ω W :=
  product_mixed_finite_budget_transfer_of_local_ae hΩ hf F
    (Eventually.of_forall (fun p _ => congrFun hF0 p)) hFY hFT α β hab

end TheoremT.Continuum.WeakGrushin
