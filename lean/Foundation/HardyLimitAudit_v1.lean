import HardyLimitComplexL2_v1

/-! Final statement audit: expose the actual Euclidean domain, Lebesgue measure,
complex wavefunction, and each coordinate basis vector without project abbreviations. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace TheoremT.HardyAudit

theorem complex_hardy_expanded
    {u : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u) :
    Integrable (fun x : EuclideanSpace ℝ (Fin 3) => ‖u x‖^2 / ‖x‖^2) volume ∧
      (∫ x : EuclideanSpace ℝ (Fin 3), ‖u x‖^2 / ‖x‖^2 ∂volume) ≤
        4 * (∫ x : EuclideanSpace ℝ (Fin 3),
          ∑ i : Fin 3, ‖fderiv ℝ u x (EuclideanSpace.single i 1)‖^2 ∂volume) :=
  TheoremT.Hardy.complex_hardy_integrable_sq_and_bound hu huc

theorem complex_multiplier_expanded
    {u : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u) :
    MemLp (fun x : EuclideanSpace ℝ (Fin 3) => u x / (‖x‖ : ℂ)) 2 volume ∧
      (∫ x : EuclideanSpace ℝ (Fin 3), ‖u x / (‖x‖ : ℂ)‖^2 ∂volume) ≤
        4 * (∫ x : EuclideanSpace ℝ (Fin 3),
          ∑ i : Fin 3, ‖fderiv ℝ u x (EuclideanSpace.single i 1)‖^2 ∂volume) :=
  TheoremT.Hardy.complex_hardy_memLp_two_and_bound hu huc

set_option pp.proofs false in
#print complex_hardy_expanded
#print axioms complex_hardy_expanded
set_option pp.proofs false in
#print complex_multiplier_expanded
#print axioms complex_multiplier_expanded
end TheoremT.HardyAudit
