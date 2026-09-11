import HardyRegularized_v1

noncomputable section
open MeasureTheory
open scoped BigOperators RealInnerProductSpace
namespace TheoremT.Hardy

theorem regularizedField_divergence {δ : ℝ} (hδ : 0 < δ) (x : R3) :
    (∑ i : Fin 3, fderiv ℝ (regularizedField δ i) x (basisVector i)) =
      (‖x‖ ^ 2 + 3 * δ) / (‖x‖ ^ 2 + δ)^2 := by
  simp_rw [regularizedField_directional_derivative hδ]
  have hs : ‖x‖ ^ 2 = (x 0)^2 + (x 1)^2 + (x 2)^2 := by
    simpa [EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ, Real.norm_eq_abs,
      sq_abs, add_assoc] using EuclideanSpace.norm_sq_eq x
  simp only [Fin.sum_univ_succ, Fin.isValue, Fin.coeSucc_eq_succ, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, Fin.sum_univ_zero, add_zero]
  field_simp [(regularizedDenominator_pos hδ x).ne']
  nlinarith [hs]

theorem integral_fderiv_compact {u : R3 → ℝ}
    (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u) (v : R3) :
    (∫ x, fderiv ℝ u x v) = 0 := by
  have h := integral_mul_fderiv_compact hu (contDiff_const (c := (1 : ℝ))) huc v
  simpa using h.symm

def weightedField (δ : ℝ) (u : R3 → ℝ) (i : Fin 3) (x : R3) : ℝ :=
  (u x)^2 * regularizedField δ i x

theorem weightedField_contDiff {δ : ℝ} (hδ : 0 < δ) {u : R3 → ℝ}
    (hu : ContDiff ℝ 1 u) (i : Fin 3) : ContDiff ℝ 1 (weightedField δ u i) :=
  (hu.pow 2).mul (regularizedField_contDiff hδ i)

theorem weightedField_compact {δ : ℝ} {u : R3 → ℝ}
    (huc : HasCompactSupport u) (i : Fin 3) : HasCompactSupport (weightedField δ u i) := by
  unfold weightedField
  simp only [sq]
  exact (huc.mul_right (f' := u)).mul_right (f' := regularizedField δ i)

theorem weightedField_directional_derivative {δ : ℝ} (hδ : 0 < δ)
    {u : R3 → ℝ} (hu : ContDiff ℝ 1 u) (i : Fin 3) (x : R3) :
    fderiv ℝ (weightedField δ u i) x (basisVector i) =
      2 * u x * fderiv ℝ u x (basisVector i) * regularizedField δ i x +
      (u x)^2 * ((‖x‖ ^ 2 + δ)⁻¹ - 2 * (x i)^2 * ((‖x‖ ^ 2 + δ)^2)⁻¹) := by
  have hd := (hu.differentiable (by norm_num) x).hasFDerivAt
  have hb := ((regularizedField_contDiff hδ i).differentiable (by norm_num) x).hasFDerivAt
  have hh := (hd.mul hd).mul hb
  change HasFDerivAt (𝕜 := ℝ) (fun y : R3 => u y * u y * regularizedField δ i y) _ x at hh
  simp only [← sq] at hh
  unfold weightedField
  rw [hh.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    Pi.pow_apply]
  rw [regularizedField_directional_derivative hδ]
  ring

theorem weightedField_divergence_integral {δ : ℝ} (hδ : 0 < δ)
    {u : R3 → ℝ} (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u) :
    (∫ x, ∑ i : Fin 3, fderiv ℝ (weightedField δ u i) x (basisVector i)) = 0 := by
  rw [integral_finset_sum]
  · simp_rw [integral_fderiv_compact (weightedField_contDiff hδ hu _)
      (weightedField_compact huc _)]
    simp
  · intro i _
    exact (((weightedField_contDiff hδ hu i).continuous_fderiv_apply (by norm_num)).comp
      (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
        ((weightedField_compact huc i).fderiv_apply ℝ (basisVector i))

#print axioms regularizedField_divergence
#print axioms integral_fderiv_compact
#print axioms weightedField_directional_derivative
#print axioms weightedField_divergence_integral
end TheoremT.Hardy
