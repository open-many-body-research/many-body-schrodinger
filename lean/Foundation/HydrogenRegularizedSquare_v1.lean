import HydrogenRegularized_v1

noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory
open scoped BigOperators
namespace TheoremT.Hydrogen
open TheoremT.Hardy

theorem radial_square_identity {δ : ℝ} (hδ : 0 < δ) (t : ℝ)
    {u : R3 → ℝ} (hu : ContDiff ℝ 1 u) (x : R3) :
    ((∑ i : Fin 3, (fderiv ℝ u x (basisVector i))^2) + t^2 * (u x)^2 +
      t * (∑ i : Fin 3, fderiv ℝ (radialWeightedField δ u i) x (basisVector i)) -
      2 * t * (u x)^2 / Real.sqrt (‖x‖^2 + δ)) * (Real.sqrt (‖x‖^2 + δ))^3 =
    (∑ i : Fin 3, (Real.sqrt (‖x‖^2 + δ) * fderiv ℝ u x (basisVector i) +
      t * u x * x i)^2) * Real.sqrt (‖x‖^2 + δ) +
      t^2 * (u x)^2 * δ * Real.sqrt (‖x‖^2 + δ) + t * (u x)^2 * δ := by
  simp_rw [radialWeightedField_directional_derivative hδ hu]
  have hs : ‖x‖ ^ 2 = (x 0)^2 + (x 1)^2 + (x 2)^2 := by
    simpa [Fin.sum_univ_succ, Real.norm_eq_abs, sq_abs, add_assoc]
      using EuclideanSpace.norm_sq_eq x
  have hd := (Real.sqrt_pos.2 (regularizedDenominator_pos hδ x)).ne'
  have he := Real.sq_sqrt (le_of_lt (regularizedDenominator_pos hδ x))
  unfold radialField
  simp only [Fin.sum_univ_succ, Fin.isValue, Fin.coeSucc_eq_succ, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, Fin.sum_univ_zero, add_zero]
  field_simp [hd]
  have he2 : (Real.sqrt (‖x‖^2 + δ))^2 = (x 0)^2 + (x 1)^2 + (x 2)^2 + δ :=
    he.trans (congrArg (fun a : ℝ => a + δ) hs)
  linear_combination (t^2 * (u x)^2 * Real.sqrt (‖x‖^2 + δ) + t * (u x)^2) * he2

theorem regularized_coulomb_pointwise {δ t : ℝ} (hδ : 0 < δ) (ht : 0 ≤ t)
    {u : R3 → ℝ} (hu : ContDiff ℝ 1 u) (x : R3) :
    2 * t * (u x)^2 / Real.sqrt (‖x‖^2 + δ) ≤
      (∑ i : Fin 3, (fderiv ℝ u x (basisVector i))^2) + t^2 * (u x)^2 +
      t * (∑ i : Fin 3, fderiv ℝ (radialWeightedField δ u i) x (basisVector i)) := by
  have h := radial_square_identity hδ t hu x
  have hp : 0 < (Real.sqrt (‖x‖^2 + δ))^3 :=
    pow_pos (Real.sqrt_pos.2 (regularizedDenominator_pos hδ x)) _
  have hn : 0 ≤ (∑ i : Fin 3, (Real.sqrt (‖x‖^2 + δ) *
      fderiv ℝ u x (basisVector i) + t * u x * x i)^2) * Real.sqrt (‖x‖^2 + δ) +
      t^2 * (u x)^2 * δ * Real.sqrt (‖x‖^2 + δ) + t * (u x)^2 * δ := by
    positivity
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_right hp).mp (h.symm ▸ hn))

#print axioms radial_square_identity
#print axioms regularized_coulomb_pointwise
end TheoremT.Hydrogen
