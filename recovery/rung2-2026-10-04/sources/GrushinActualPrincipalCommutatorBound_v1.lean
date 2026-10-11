import GrushinQuadraticPrincipalIdentification_v1
import WeakGrushinMixedMultiIndexEquation_v1

/-! Closed principal formula and actual R15 norm bound for the quadratic
term in the canonical differentiated weak PDE. The algebraic identification
has no jet hypotheses; the norm estimate retains exactly the supplied
lower shifted outer representatives and bounds of the functional theorem.
-/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace TheoremT.Continuum.WeakGrushin

theorem mixedMultiIndexGrushinSource_closed (c : ℝ) (B : Space (Fin 3) → ℝ)
    (F : FactorialRawJetFamily) (s : Space (Fin 3) → ℂ)
    (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) (p : Space (Fin 3)) :
    mixedMultiIndexGrushinSource c B F s α β p =
      complexDirectionalWordDeriv productCoordinateDirection s (mixedMultiIndexWord α β) p-
        directionalWordCommutator productCoordinateDirection B (mixedMultiIndexWordFamily F)
          (mixedMultiIndexWord α β) p+factorialPrincipalRawError c F α β p := by
  unfold mixedMultiIndexGrushinSource coordinateWordGrushinSource
  rw [grushin_quadratic_principal_identification]

theorem factorial_actual_principal_commutator_L2
    {μ : Measure (Space (Fin 3))} (c : ℝ) (F : FactorialRawJetFamily)
    (W : (Fin 4 → ℕ) → (Fin 3 → ℕ) → FactorialOuterIndex → Lp ℂ 2 μ)
    (r : ℕ) (N1 N2 : ℝ)
    (hW : ∀ a b, factorialMultiDerivativeCost a b ≤ r-1 → FactorialShiftedOuterL2Rep F W a b)
    (hN1 : ∀ a b, factorialMultiDerivativeCost a b ≤ r-1 → factorialOuterNorm (W a b) ≤ N1)
    (hN2 : ∀ a b, factorialMultiDerivativeCost a b ≤ r-2 → factorialOuterNorm (W a b) ≤ N2)
    (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) (hc : factorialMultiDerivativeCost α β ≤ r) :
    ∃ H : Lp ℂ 2 μ,
      H =ᵐ[μ] (fun p => c • directionalWordCommutator productCoordinateDirection
        (fun q : Space (Fin 3) => ‖q.1‖^2)
        (coordinateWordSpectatorTrace (mixedMultiIndexWordFamily F)) (mixedMultiIndexWord α β) p) ∧
      ‖H‖ ≤ 6*|c| *(r : ℝ)*N1+3*|c| *((r*(r-1) : ℕ) : ℝ)*N2 := by
  obtain ⟨H,hH,hN⟩ := factorial_principal_indexed_error_L2 c F W r N1 N2 hW hN1 hN2 α β hc
  refine ⟨H,?_,hN⟩
  exact hH.trans (Eventually.of_forall (fun p => (grushin_quadratic_principal_identification c F α β p).symm))

#print axioms mixedMultiIndexGrushinSource_closed
#print axioms factorial_actual_principal_commutator_L2
end TheoremT.Continuum.WeakGrushin
