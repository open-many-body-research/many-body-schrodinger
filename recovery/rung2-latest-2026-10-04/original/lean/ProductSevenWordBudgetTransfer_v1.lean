import ProductSevenPullbackL2Budget_v1
import SmoothCoordinateSubsetFields7_v1

/-! The local L2 word budgets supply exactly the mixed subset budgets used
by the quantitative smooth-representative theorem on the ordinary coordinate box. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
namespace TheoremT.Continuum
open WeakGrushin

theorem product_seven_word_budgets_of_local_L2_norms
    {K : Set (Fin 7 → ℝ)} {Ω : Set (Space (Fin 3))}
    (hK : MapsTo sevenToProduct K Ω)
    (D : List (Fin 4 ⊕ Fin 3) → Space (Fin 3) → ℂ)
    (hD : ∀ v, MemLp (D v) 2 (volume.restrict Ω))
    (M : List (Fin 7) → ℝ)
    (hDM : ∀ w s, (eLpNorm (D ((canonicalSubsetWord7 s ++ w).map sevenCoordinateEquiv))
      2 (volume.restrict Ω)).toReal ≤ M w) :
    ∀ w s, Real.sqrt (∫ x in K,
      ‖D ((canonicalSubsetWord7 s ++ w).map sevenCoordinateEquiv) (sevenToProduct x)‖^2) ≤ M w := by
  intro w s
  exact (sevenToProduct_sqrt_integral_le_eLpNorm hK (hD _)).trans (hDM w s)

theorem product_seven_word_budgets_of_region_budgets
    {K : Set (Fin 7 → ℝ)} {Ω : Set (Space (Fin 3))}
    (hK : MapsTo sevenToProduct K Ω)
    (D : List (Fin 4 ⊕ Fin 3) → Space (Fin 3) → ℂ)
    (M : List (Fin 7) → ℝ) (hM : ∀ w, 0 ≤ M w)
    (hDM : ∀ w s, RegionL2Budget
      (D ((canonicalSubsetWord7 s ++ w).map sevenCoordinateEquiv)) Ω ((M w)^2)) :
    ∀ w s, Real.sqrt (∫ x in K,
      ‖D ((canonicalSubsetWord7 s ++ w).map sevenCoordinateEquiv) (sevenToProduct x)‖^2) ≤ M w := by
  intro w s
  exact sevenToProduct_regionL2Budget_sq hK (hM w) (hDM w s)

end TheoremT.Continuum
