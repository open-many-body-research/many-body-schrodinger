import GrushinQuadraticCountedCommutator_v1
import ProductCoordinateWordSpectatorTrace_v1
import GrushinFactorialPrincipalIndexedBound_v1

/-! Pointwise identification of the actual quadratic coefficient commutator
with the exact raw principal error used by the sealed functional bound.
This is an algebraic identity for every raw natural family, with no weak
derivative, norm, compatibility or differentiated-equation premise. -/
noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum.WeakGrushin

theorem coordinateWordSpectatorTrace_counted_family
    (F : (Fin 4 → ℕ) → (Fin 3 → ℕ) → Space (Fin 3) → ℂ) :
    coordinateWordSpectatorTrace (mixedMultiIndexWordFamily F) =
      mixedMultiIndexWordFamily (fun α β p => ∑ j : Fin 3, F α (β + Pi.single j 2) p) := by
  funext w p
  change (∑ j : Fin 3, mixedMultiIndexWordFamily F (w ++ [Sum.inr j,Sum.inr j]) p) =
    ∑ j : Fin 3, F (factorialWordYCount w) (factorialWordTCount w + Pi.single j 2) p
  apply Finset.sum_congr rfl
  intro j _
  exact congrFun (mixedMultiIndexWordFamily_append_tt F w j) p

theorem grushin_quadratic_principal_identification
    (c : ℝ) (F : FactorialRawJetFamily)
    (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) (p : Space (Fin 3)) :
    c • directionalWordCommutator productCoordinateDirection
      (fun q : Space (Fin 3) => ‖q.1‖^2)
      (coordinateWordSpectatorTrace (mixedMultiIndexWordFamily F))
      (mixedMultiIndexWord α β) p = factorialPrincipalRawError c F α β p := by
  rw [coordinateWordSpectatorTrace_counted_family, grushin_quadratic_counted_commutator,
    factorialWordYCount_mixedMultiIndexWord, factorialWordTCount_mixedMultiIndexWord]
  simp only [factorialPrincipalRawError, smul_add, smul_smul, Finset.smul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    ring

end TheoremT.Continuum.WeakGrushin
