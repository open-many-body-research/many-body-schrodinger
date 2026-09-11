import HalfLineFactors_v1

/-! The form in the factorization is the actual singular half-line integral,
which is finite on every input of the declared domain. -/
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Set Filter
open scoped Topology
namespace TheoremT.HalfLine

theorem coulombMoment_integrable (u : D) :
    Integrable (fun x => ‖J u x‖^2 / x) μ := by
  apply (L2.integrable_inner (𝕜 := ℝ) (W u) (J u)).congr
  filter_upwards [W_coe u] with x hx
  rw [hx, real_inner_smul_left, real_inner_self_eq_norm_sq]
  ring

theorem coulombMoment_integral (u : D) :
    coulombMoment u = ∫ x, ‖J u x‖^2 / x ∂μ := by
  unfold coulombMoment
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [W_coe u] with x hx
  rw [hx, real_inner_smul_left, real_inner_self_eq_norm_sq]
  ring

theorem coulombMoment_nonneg (u : D) : 0 ≤ coulombMoment u := by
  rw [coulombMoment_integral]
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact div_nonneg (sq_nonneg _) hx.le

theorem coulombMoment_bound (u : D) :
    coulombMoment u ≤ 2 * ‖dJ u‖ * ‖J u‖ := by
  exact (real_inner_le_norm (W u) (J u)).trans
    (mul_le_mul_of_nonneg_right (hardy_domain u) (norm_nonneg _))

theorem q_physical (Z : ℝ) (u : D) :
    q Z u = (1/2) * ‖dJ u‖^2 - Z * ∫ x, ‖J u x‖^2 / x ∂μ := by
  rw [q, coulombMoment_integral]

theorem q_lower (Z : ℝ) (u : D) : -(Z^2/2) * ‖J u‖^2 ≤ q Z u := by
  rw [q_square_A]
  nlinarith [sq_nonneg ‖A Z u‖]

#print axioms coulombMoment_integrable
#print axioms coulombMoment_integral
#print axioms coulombMoment_nonneg
#print axioms coulombMoment_bound
#print axioms q_physical
#print axioms q_lower
end TheoremT.HalfLine
