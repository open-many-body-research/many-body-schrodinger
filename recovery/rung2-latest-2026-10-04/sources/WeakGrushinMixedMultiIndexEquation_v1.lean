import WeakGrushinCoordinateWordEquation_v1
import ProductMixedMultiIndexWordFamily_v1
import SmoothComplexMixedSourceWords_v1

/-! Actual canonical natural-multiindex Grushin equations. The source uses
ordinary smooth coefficient/source derivatives and the exact counted natural
solution family. No equation for a positive-order jet is assumed. The proper
quadratic term remains an exact ordered split sum at this stage; its closed
multiindex formula and quantitative bounds are separate obligations.
-/
noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin

def mixedMultiIndexGrushinSource (c : ℝ) (B : Space (Fin 3) → ℝ)
    (F : (Fin 4 → ℕ) → (Fin 3 → ℕ) → Space (Fin 3) → ℂ)
    (s : Space (Fin 3) → ℂ) (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) : Space (Fin 3) → ℂ :=
  coordinateWordGrushinSource c B (mixedMultiIndexWordFamily F)
    (complexDirectionalWordDeriv productCoordinateDirection s) (mixedMultiIndexWord α β)

theorem weak_grushin_mixed_multiIndex_equations
    (c : ℝ) {Ω : Set (Space (Fin 3))} (hΩ : IsOpen Ω)
    {B : Space (Fin 3) → ℝ} (hB : ContDiffOn ℝ ∞ B Ω)
    {s : Space (Fin 3) → ℂ} (hs : ContDiffOn ℝ ∞ s Ω) {m : ℕ} {W : ℝ}
    (F : (Fin 4 → ℕ) → (Fin 3 → ℕ) → Space (Fin 3) → ℂ)
    (hF : ∀ α β, (∑ i,α i)+(∑ j,β j) ≤ m+2 → RegionL2Budget (F α β) Ω W)
    (hY : ∀ α β i, (∑ k,α k)+(∑ j,β j) < m+2 →
      ProductLocalWeakDirectional Ω (F α β) (F (α+Pi.single i 1) β) (yDir i))
    (hT : ∀ α β j, (∑ i,α i)+(∑ k,β k) < m+2 →
      ProductLocalWeakDirectional Ω (F α β) (F α (β+Pi.single j 1)) (tDir j))
    (hP : ∀ φ : Space (Fin 3) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c oscillatorBasis B φ p • F 0 0 p) = ∫ p,φ p • s p) :
    ∀ α β, (∑ i,α i)+(∑ j,β j) ≤ m →
      ProductLocallyL2On (mixedMultiIndexGrushinSource c B F s α β) Ω ∧
      ∀ φ : Space (Fin 3) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
        Integrable (fun p => splitGrushin c oscillatorBasis B φ p • F α β p) ∧
        Integrable (fun p => φ p • mixedMultiIndexGrushinSource c B F s α β p) ∧
        (∫ p, splitGrushin c oscillatorBasis B φ p • F α β p) =
          ∫ p,φ p • mixedMultiIndexGrushinSource c B F s α β p := by
  have hSL (w : List (Fin 4 ⊕ Fin 3)) (_ : w.length ≤ m) :
      ProductLocallyL2On (complexDirectionalWordDeriv productCoordinateDirection s w) Ω :=
    product_continuousOn_locallyL2
      (complexDirectionalWordDeriv_contDiffOn productCoordinateDirection hΩ hs w).continuousOn
  have hSD (w : List (Fin 4 ⊕ Fin 3)) (i : Fin 4 ⊕ Fin 3) (_ : w.length < m) :
      ProductLocalWeakDirectional Ω (complexDirectionalWordDeriv productCoordinateDirection s w)
        (complexDirectionalWordDeriv productCoordinateDirection s (i :: w))
        (productCoordinateDirection i) :=
    complex_smooth_local_weak_directional hΩ
      (complexDirectionalWordDeriv_contDiffOn productCoordinateDirection hΩ hs w) _
  have hEq := weak_grushin_coordinate_word_equations c hΩ hB
    (mixedMultiIndexWordFamily F) (complexDirectionalWordDeriv productCoordinateDirection s)
    (mixedMultiIndexWordFamily_budget F hF) (mixedMultiIndexWordFamily_localD F hY hT)
    hSL hSD (by simpa only [mixedMultiIndexWordFamily_nil,complexDirectionalWordDeriv] using hP)
  intro α β hab
  simpa only [mixedMultiIndexWordFamily_canonical,mixedMultiIndexGrushinSource] using
    hEq (mixedMultiIndexWord α β) (by rwa [mixedMultiIndexWord_length])

#print axioms mixedMultiIndexGrushinSource
#print axioms weak_grushin_mixed_multiIndex_equations
end TheoremT.Continuum.WeakGrushin
