import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Analytic.ConvergenceRadius
import Mathlib.Tactic

/-! All-order center bounds for actual iterated Frechet derivatives.
The factorial arises from the full permutation sum of the multilinear
coefficient. Analyticity supplies the geometric coefficient bound; no finite
smooth-jet compactness hypothesis is used or promoted to an all-order claim.
-/
noncomputable section
open scoped BigOperators ENNReal NNReal
namespace TheoremT.Continuum

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {f : E → F} {p : FormalMultilinearSeries ℝ E F} {x : E} {R : ℝ≥0∞}

theorem powerSeries_iteratedFDeriv_eq_permutation_sum
    (hf : HasFPowerSeriesOnBall f p x R) (k : ℕ) :
    iteratedFDeriv ℝ k f x =
      ∑ sigma : Equiv.Perm (Fin k), (p k).domDomCongr sigma := by
  ext v
  simpa only [sum_apply, ContinuousMultilinearMap.domDomCongr_apply]
    using hf.iteratedFDeriv_eq_sum_of_completeSpace v

theorem powerSeries_norm_iteratedFDeriv_le_factorial_coeff
    (hf : HasFPowerSeriesOnBall f p x R) (k : ℕ) :
    ‖iteratedFDeriv ℝ k f x‖ ≤ (k.factorial : ℝ) * ‖p k‖ := by
  rw [powerSeries_iteratedFDeriv_eq_permutation_sum hf]
  calc
    ‖∑ sigma : Equiv.Perm (Fin k), (p k).domDomCongr sigma‖ ≤
        ∑ sigma : Equiv.Perm (Fin k), ‖(p k).domDomCongr sigma‖ := norm_sum_le _ _
    _ = (k.factorial : ℝ) * ‖p k‖ := by
      simp [ContinuousMultilinearMap.norm_domDomCongr, Fintype.card_perm]

theorem powerSeries_center_factorial_radius_bound
    (hf : HasFPowerSeriesOnBall f p x R) {r : ℝ≥0}
    (hr : 0 < r) (hrp : (r : ℝ≥0∞) < p.radius) :
    ∃ C > 0, ∀ k : ℕ,
      ‖iteratedFDeriv ℝ k f x‖ ≤ (k.factorial : ℝ) * (C / (r : ℝ)^k) := by
  obtain ⟨C,hC,hp⟩ := p.norm_le_div_pow_of_pos_of_lt_radius hr hrp
  refine ⟨C,hC,fun k => ?_⟩
  exact (powerSeries_norm_iteratedFDeriv_le_factorial_coeff hf k).trans
    (mul_le_mul_of_nonneg_left (hp k) (Nat.cast_nonneg _))

theorem analyticAt_center_factorial_bound (hf : AnalyticAt ℝ f x) :
    ∃ C > 0, ∃ A > 0, ∀ k : ℕ,
      ‖iteratedFDeriv ℝ k f x‖ ≤ C * A^k * (k.factorial : ℝ) := by
  obtain ⟨p,R,hp⟩ := hf
  obtain ⟨r,hr0,hrR⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp.r_pos
  have hr : 0 < r := by exact_mod_cast hr0
  obtain ⟨C,hC,hbound⟩ := powerSeries_center_factorial_radius_bound hp hr (hrR.trans_le hp.r_le)
  refine ⟨C,hC,(r : ℝ)⁻¹,inv_pos.mpr hr,fun k => ?_⟩
  simpa only [div_eq_mul_inv, inv_pow, mul_comm, mul_left_comm, mul_assoc] using hbound k

end TheoremT.Continuum
