import ManyBody.S8.Internal.AnisotropicCoordinateScaling
import ManyBody.S8.Internal.PhysicalComplexDerivativeTransport
import Mathlib.Tactic
/-! Transport of anisotropic mixed derivative estimates to genuine real
Euclidean physical directions. The coordinate map is only used through its
proved block contractions and exact real/complex derivative transport. -/
noncomputable section
open scoped BigOperators
namespace ManyBody.S8
open TheoremT.Continuum MixedAnalytic

theorem blockDirectionWeight_physical_le (D S : ℝ) (hD : 0 ≤ D) (hS : 0 ≤ S)
    (v : Position × Position) :
    blockDirectionWeight D S (physicalComplexCoordinatesCLM v) ≤
      max (D*‖v.1‖) (S*‖v.2‖) := by
  apply max_le_max
  · exact mul_le_mul_of_nonneg_left (physicalComplexCoordinatesCLM_left_norm_le v) hD
  · exact mul_le_mul_of_nonneg_left (physicalComplexCoordinatesCLM_right_norm_le v) hS

theorem physical_centered_anisotropic_derivative_bound
    {f : (Fin 3 ⊕ Fin 3 → ℂ) → ℂ} (t0 : Position) {x : Position × Position}
    (hf : AnalyticAt ℂ f (physicalComplexCoordinatesAt t0 x))
    {D S K : ℝ} (hD : 0 ≤ D) (hS : 0 ≤ S) (hK : 0 ≤ K)
    (n : ℕ)
    (hbound : ∀ dirs : Fin n → (Fin 3 ⊕ Fin 3 → ℂ),
      ‖iteratedFDeriv ℂ n f (physicalComplexCoordinatesAt t0 x) dirs‖ ≤
        K*∏ i, blockDirectionWeight D S (dirs i))
    (v : Fin n → Position × Position) :
    ‖iteratedFDeriv ℝ n (f ∘ physicalComplexCoordinatesAt t0) x v‖ ≤
      K*∏ i, max (D*‖(v i).1‖) (S*‖(v i).2‖) := by
  rw [physical_centered_iteratedFDeriv_complex_restriction t0 hf n v]
  apply (hbound (fun i => physicalComplexCoordinatesCLM (v i))).trans
  apply mul_le_mul_of_nonneg_left _ hK
  apply Finset.prod_le_prod₀
  · intro i _
    exact (mul_nonneg hD (norm_nonneg _)).trans (le_max_left _ _)
  · intro i _
    exact blockDirectionWeight_physical_le D S hD hS (v i)

#print axioms blockDirectionWeight_physical_le
#print axioms physical_centered_anisotropic_derivative_bound
end ManyBody.S8
