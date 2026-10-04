import WeakGrushinMixedMultiIndexEquation_v1

/-! Differentiated Grushin equations constructed from raw local data.
For every finite order the original equation and local smooth coefficient
and source produce one genuine natural-index weak jet family on an interior
box. No solution derivative is an input. The derivative equations contain
exact ordered commutators, with local L2 and both test integrabilities proved.
The finite common budget depends on the requested order; no uniform-order,
factorial, efficient-computation or classical-representative claim is made.
-/
noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin

theorem local_smooth_weak_grushin_differentiated_equations
    {Ω : Set (Space (Fin 3))} (hΩ : IsOpen Ω)
    (a : Space (Fin 3)) {aY aT bY bT c : ℝ}
    (hby : 0 < bY) (hbt : 0 < bT) (hy : bY < aY) (ht : bT < aT)
    (hKΩ : rectangularClosedBox a aY aT ⊆ Ω) (hc : 0 < c)
    {B : Space (Fin 3) → ℝ} (hB : ContDiffOn ℝ ∞ B Ω)
    {s : Space (Fin 3) → ℂ} (hs : ContDiffOn ℝ ∞ s Ω)
    {f : Space (Fin 3) → ℂ} (hf : ProductLocallyL2On f Ω)
    (hEq : ∀ φ : Space (Fin 3) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c oscillatorBasis B φ p • f p) = ∫ p,φ p • s p)
    (m : ℕ) : ∃ (W : ℝ) (F : (Fin 4 → ℕ) → (Fin 3 → ℕ) → Space (Fin 3) → ℂ),
      0 ≤ W ∧ F 0 0 = f ∧
      (∀ α β, (∑ i,α i)+(∑ j,β j) ≤ m+2 →
        RegionL2Budget (F α β) (rectangularOpenBox a bY bT) W) ∧
      (∀ α β i, (∑ k,α k)+(∑ j,β j) < m+2 →
        ProductLocalWeakDirectional (rectangularOpenBox a bY bT)
          (F α β) (F (α+Pi.single i 1) β) (yDir i)) ∧
      (∀ α β j, (∑ i,α i)+(∑ k,β k) < m+2 →
        ProductLocalWeakDirectional (rectangularOpenBox a bY bT)
          (F α β) (F α (β+Pi.single j 1)) (tDir j)) ∧
      ∀ α β, (∑ i,α i)+(∑ j,β j) ≤ m →
        ProductLocallyL2On (mixedMultiIndexGrushinSource c B F s α β)
          (rectangularOpenBox a bY bT) ∧
        ∀ φ : Space (Fin 3) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
          tsupport φ ⊆ rectangularOpenBox a bY bT →
          Integrable (fun p => splitGrushin c oscillatorBasis B φ p • F α β p) ∧
          Integrable (fun p => φ p • mixedMultiIndexGrushinSource c B F s α β p) ∧
          (∫ p, splitGrushin c oscillatorBasis B φ p • F α β p) =
            ∫ p,φ p • mixedMultiIndexGrushinSource c B F s α β p := by
  obtain ⟨W,hW,F,h0,hF,hY,hT⟩ := local_smooth_weak_grushin_mixed_multiIndex_regularity
    hΩ a hby hbt hy ht hKΩ hc hB hs hf hEq (m+2)
  have hInner : rectangularOpenBox a bY bT ⊆ Ω :=
    (rectangularOpenBox_subset_closedBox a bY bT).trans
      ((rectangularClosedBox_subset_openBox a hy ht).trans
        ((rectangularOpenBox_subset_closedBox a aY aT).trans hKΩ))
  refine ⟨W,F,hW,h0,hF,hY,hT,?_⟩
  exact weak_grushin_mixed_multiIndex_equations c (rectangularOpenBox_isOpen a bY bT)
    (hB.mono hInner) (hs.mono hInner) F hF hY hT
    (fun φ hφ hφc hφs => by
      simpa only [h0] using hEq φ hφ hφc (hφs.trans hInner))

#print axioms local_smooth_weak_grushin_differentiated_equations
end TheoremT.Continuum.WeakGrushin
