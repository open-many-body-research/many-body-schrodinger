import ProductMixedAllOrderWeakFamily_v1
import WeakGrushinMixedMultiIndexEquation_v1

/-! One actual all-order weak family and all of its differentiated equations
from the original local Grushin equation. Each finite norm budget exists
after its order; no factorial bound, smooth representative or algorithm is
assumed or concluded. -/
noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin

theorem local_weak_grushin_allOrder_equations
    {Ω : Set (Space (Fin 3))} (hΩ : IsOpen Ω)
    (a : Space (Fin 3)) {aY aT bY bT c : ℝ}
    (hby : 0 < bY) (hbt : 0 < bT) (hy : bY < aY) (ht : bT < aT)
    (hKΩ : rectangularClosedBox a aY aT ⊆ Ω) (hc : 0 < c)
    {B : Space (Fin 3) → ℝ} (hB : ContDiffOn ℝ ∞ B Ω)
    {s : Space (Fin 3) → ℂ} (hs : ContDiffOn ℝ ∞ s Ω)
    {f : Space (Fin 3) → ℂ} (hf : ProductLocallyL2On f Ω)
    (hEq : ∀ φ : Space (Fin 3) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c oscillatorBasis B φ p • f p) = ∫ p,φ p • s p) :
    ∃ F : (Fin 4 → ℕ) → (Fin 3 → ℕ) → Space (Fin 3) → ℂ,
      F 0 0 = f ∧
      (∀ m : ℕ, ∃ W : ℝ, 0 ≤ W ∧ ∀ α β,
        (∑ i,α i)+(∑ j,β j) ≤ m →
          RegionL2Budget (F α β) (rectangularOpenBox a bY bT) W) ∧
      (∀ α β i, ProductLocalWeakDirectional (rectangularOpenBox a bY bT)
        (F α β) (F (α+Pi.single i 1) β) (yDir i)) ∧
      (∀ α β j, ProductLocalWeakDirectional (rectangularOpenBox a bY bT)
        (F α β) (F α (β+Pi.single j 1)) (tDir j)) ∧
      ∀ α β,
        ProductLocallyL2On (mixedMultiIndexGrushinSource c B F s α β)
          (rectangularOpenBox a bY bT) ∧
        ∀ φ : Space (Fin 3) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
          tsupport φ ⊆ rectangularOpenBox a bY bT →
          Integrable (fun p => splitGrushin c oscillatorBasis B φ p • F α β p) ∧
          Integrable (fun p => φ p • mixedMultiIndexGrushinSource c B F s α β p) ∧
          (∫ p, splitGrushin c oscillatorBasis B φ p • F α β p) =
            ∫ p,φ p • mixedMultiIndexGrushinSource c B F s α β p := by
  obtain ⟨F,h0,hBudget,hY,hT⟩ := local_smooth_weak_grushin_allOrder_family
    hΩ a hby hbt hy ht hKΩ hc hB hs hf hEq
  have hInner : rectangularOpenBox a bY bT ⊆ Ω :=
    (rectangularOpenBox_subset_closedBox a bY bT).trans
      ((rectangularClosedBox_subset_openBox a hy ht).trans
        ((rectangularOpenBox_subset_closedBox a aY aT).trans hKΩ))
  refine ⟨F,h0,hBudget,hY,hT,?_⟩
  intro α β
  let m := (∑ i,α i)+(∑ j,β j)
  obtain ⟨W,hW,hF⟩ := hBudget (m+2)
  exact weak_grushin_mixed_multiIndex_equations c (rectangularOpenBox_isOpen a bY bT)
    (hB.mono hInner) (hs.mono hInner) F hF
    (fun a b i _ => hY a b i) (fun a b j _ => hT a b j)
    (fun φ hφ hφc hφs => by
      simpa only [h0] using hEq φ hφ hφc (hφs.trans hInner)) α β le_rfl

end TheoremT.Continuum.WeakGrushin
