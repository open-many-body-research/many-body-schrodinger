import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Tactic

/-! Exact complex iterated Frechet derivatives at the center of an actual
power-series representation. The permutation sum and factorial coefficient
bound are derived from the same supplied series; no geometric coefficient
bound or merely existential local analyticity estimate is asserted here. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators ENNReal
namespace TheoremT.Continuum

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {f : E → F} {p : FormalMultilinearSeries ℂ E F} {x : E} {R : ℝ≥0∞}

theorem complex_powerSeries_iteratedFDeriv_eq_permutation_sum
    (hf : HasFPowerSeriesOnBall f p x R) (k : ℕ) :
    iteratedFDeriv ℂ k f x =
      ∑ sigma : Equiv.Perm (Fin k), (p k).domDomCongr sigma := by
  ext v
  simpa only [sum_apply, ContinuousMultilinearMap.domDomCongr_apply]
    using hf.iteratedFDeriv_eq_sum_of_completeSpace v

theorem complex_powerSeries_norm_iteratedFDeriv_le_factorial_coeff
    (hf : HasFPowerSeriesOnBall f p x R) (k : ℕ) :
    ‖iteratedFDeriv ℂ k f x‖ ≤ (k.factorial : ℝ) * ‖p k‖ := by
  rw [complex_powerSeries_iteratedFDeriv_eq_permutation_sum hf]
  calc
    ‖∑ sigma : Equiv.Perm (Fin k), (p k).domDomCongr sigma‖ ≤
        ∑ sigma : Equiv.Perm (Fin k), ‖(p k).domDomCongr sigma‖ := norm_sum_le _ _
    _ = (k.factorial : ℝ) * ‖p k‖ := by
      simp [ContinuousMultilinearMap.norm_domDomCongr, Fintype.card_perm]

end TheoremT.Continuum
