import ScaledCutoff_v2

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace TheoremT.Continuum

def baseCutoffPartial (N : ℕ) (k : Coordinate N) (x : Configuration N) : ℝ :=
  fderiv ℝ (smoothCutoffBase N) x (coordinateVector k)

theorem baseCutoffPartial_contDiff (N : ℕ) (k : Coordinate N) :
    ContDiff ℝ ∞ (baseCutoffPartial N k) := by
  have hb : ContDiff ℝ ∞ (smoothCutoffBase N) := (smoothCutoffBase N).contDiff
  exact (hb.fderiv_right (by simp : (∞ : WithTop ℕ∞) + 1 ≤ ∞)).clm_apply contDiff_const

theorem baseCutoffPartial_hasCompactSupport (N : ℕ) (k : Coordinate N) :
    HasCompactSupport (baseCutoffPartial N k) :=
  (smoothCutoffBase N).hasCompactSupport.fderiv_apply ℝ (coordinateVector k)

theorem scaledCutoff_secondPartial (N : ℕ) (R : ℝ) (x : Configuration N)
    (k l : Coordinate N) :
    fderiv ℝ (fun y => fderiv ℝ (scaledCutoff N R) y (coordinateVector k)) x
      (coordinateVector l) =
    R⁻¹^2 * fderiv ℝ (baseCutoffPartial N k) (R⁻¹ • x) (coordinateVector l) := by
  have hfun : (fun y => fderiv ℝ (scaledCutoff N R) y (coordinateVector k)) =
      fun y => R⁻¹ • baseCutoffPartial N k (R⁻¹ • y) := by
    funext y
    exact scaledCutoff_partial N R y k
  rw [hfun]
  have hb := ((baseCutoffPartial_contDiff N k).differentiable (by simp) (R⁻¹ • x)).hasFDerivAt
  have hs := (hasFDerivAt_id (𝕜 := ℝ) x).const_smul R⁻¹
  have hh := (hb.comp x hs).const_smul R⁻¹
  change HasFDerivAt (𝕜 := ℝ) (fun y => R⁻¹ • baseCutoffPartial N k (R⁻¹ • y)) _ x at hh
  rw [hh.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
  ring

/-- One finite constant controls every second coordinate derivative, with the
required R^{-2} scaling. -/
theorem scaledCutoff_secondDerivative_bound (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∀ (x : Configuration N) (k l : Coordinate N),
      ‖fderiv ℝ (fun y => fderiv ℝ (scaledCutoff N R) y (coordinateVector k)) x
        (coordinateVector l)‖ ≤ C / R^2 := by
  have hex (k : Coordinate N) : ∃ C : ℝ, ∀ x, ‖fderiv ℝ (baseCutoffPartial N k) x‖ ≤ C :=
    ((baseCutoffPartial_hasCompactSupport N k).fderiv ℝ).exists_bound_of_continuous
      ((baseCutoffPartial_contDiff N k).continuous_fderiv (by simp))
  choose C hC using hex
  have hC0 (k : Coordinate N) : 0 ≤ C k := (norm_nonneg _).trans (hC k 0)
  refine ⟨∑ k, C k, Finset.sum_nonneg (fun k _ => hC0 k), fun R hR x k l => ?_⟩
  have he : ‖coordinateVector l‖ = 1 := by simp [coordinateVector]
  have hb : ‖fderiv ℝ (baseCutoffPartial N k) (R⁻¹ • x) (coordinateVector l)‖ ≤ ∑ k, C k := by
    calc _ ≤ ‖fderiv ℝ (baseCutoffPartial N k) (R⁻¹ • x)‖ * ‖coordinateVector l‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ C k := by simpa [he] using hC k (R⁻¹ • x)
      _ ≤ ∑ k, C k := Finset.single_le_sum (fun k _ => hC0 k) (Finset.mem_univ k)
  rw [scaledCutoff_secondPartial, norm_mul, norm_pow, Real.norm_eq_abs R⁻¹,
    abs_inv, abs_of_pos hR]
  simpa only [div_eq_mul_inv, inv_pow, mul_comm] using
    mul_le_mul_of_nonneg_left hb (sq_nonneg R⁻¹)

#print axioms scaledCutoff_secondPartial
#print axioms scaledCutoff_secondDerivative_bound
end TheoremT.Continuum
