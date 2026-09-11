import HardyRegularized_v2

noncomputable section
open MeasureTheory
open scoped BigOperators RealInnerProductSpace
namespace TheoremT.Hardy

theorem regularized_hardy_square_identity {δ : ℝ} (hδ : 0 < δ)
    {u : R3 → ℝ} (hu : ContDiff ℝ 1 u) (x : R3) :
    (4 * (∑ i : Fin 3, (fderiv ℝ u x (basisVector i))^2) +
      2 * (∑ i : Fin 3, fderiv ℝ (weightedField δ u i) x (basisVector i)) -
      (u x)^2 / (‖x‖^2 + δ)) * (‖x‖^2 + δ)^2 =
    (∑ i : Fin 3, (2 * (‖x‖^2 + δ) * fderiv ℝ u x (basisVector i) +
      u x * x i)^2) + 5 * δ * (u x)^2 := by
  simp_rw [weightedField_directional_derivative hδ hu]
  have hs : ‖x‖ ^ 2 = (x 0)^2 + (x 1)^2 + (x 2)^2 := by
    simpa [Fin.sum_univ_succ, Real.norm_eq_abs, sq_abs, add_assoc]
      using EuclideanSpace.norm_sq_eq x
  have hd := (regularizedDenominator_pos hδ x).ne'
  unfold regularizedField
  simp [Fin.sum_univ_succ]
  field_simp [hd]
  rw [hs]
  ring

theorem regularized_hardy_pointwise {δ : ℝ} (hδ : 0 < δ)
    {u : R3 → ℝ} (hu : ContDiff ℝ 1 u) (x : R3) :
    (u x)^2 / (‖x‖^2 + δ) ≤
      4 * (∑ i : Fin 3, (fderiv ℝ u x (basisVector i))^2) +
      2 * (∑ i : Fin 3, fderiv ℝ (weightedField δ u i) x (basisVector i)) := by
  have h := regularized_hardy_square_identity hδ hu x
  have hp : 0 < (‖x‖^2 + δ)^2 := sq_pos_of_pos (regularizedDenominator_pos hδ x)
  have hn : 0 ≤ (∑ i : Fin 3, (2 * (‖x‖^2 + δ) *
      fderiv ℝ u x (basisVector i) + u x * x i)^2) + 5 * δ * (u x)^2 := by
    positivity
  have hnonneg := (mul_nonneg_iff_of_pos_right hp).mp (h.symm ▸ hn)
  exact sub_nonneg.mp hnonneg

theorem regularized_hardy_integral {δ : ℝ} (hδ : 0 < δ)
    {u : R3 → ℝ} (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u) :
    (∫ x, (u x)^2 / (‖x‖^2 + δ)) ≤
      4 * (∫ x, ∑ i : Fin 3, (fderiv ℝ u x (basisVector i))^2) := by
  have hg : Integrable (fun x => ∑ i : Fin 3, (fderiv ℝ u x (basisVector i))^2) := by
    apply integrable_finset_sum
    intro i _
    apply ((((hu.continuous_fderiv_apply (by norm_num)).comp
      (continuous_id.prodMk continuous_const)).pow 2)).integrable_of_hasCompactSupport
    apply (huc.fderiv_apply ℝ (basisVector i)).mono
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro hz
    apply hx
    change (fderiv ℝ u x (basisVector i))^2 = 0
    rw [hz]
    norm_num
  have hw : Integrable (fun x => ∑ i : Fin 3,
      fderiv ℝ (weightedField δ u i) x (basisVector i)) := by
    apply integrable_finset_sum
    intro i _
    exact (((weightedField_contDiff hδ hu i).continuous_fderiv_apply (by norm_num)).comp
      (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
        ((weightedField_compact huc i).fderiv_apply ℝ (basisVector i))
  have hf : Integrable (fun x => (u x)^2 / (‖x‖^2 + δ)) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (hu.continuous.pow 2).div (continuous_norm.pow 2 |>.add continuous_const)
        (fun x => (regularizedDenominator_pos hδ x).ne')
    · apply huc.mono
      intro x hx
      simp only [Function.mem_support] at hx ⊢
      intro hz
      apply hx
      rw [hz]
      norm_num
  have h := integral_mono hf ((hg.const_mul 4).add (hw.const_mul 2))
    (regularized_hardy_pointwise hδ hu)
  simp only [Pi.add_apply] at h
  rw [integral_add (hg.const_mul 4) (hw.const_mul 2), integral_const_mul,
    integral_const_mul, weightedField_divergence_integral hδ hu huc] at h
  simpa using h

#print axioms regularized_hardy_integral
end TheoremT.Hardy
