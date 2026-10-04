import ManyBody.S8.Internal.PhysicalDistanceH2ErrorBudget
import CoulombDilation_v1
import CoulombTwoElectronExpectation_v1
import ActualL2IntegralCauchy_v1

/-! The actual two-electron compact Coulomb L2 budget scales quadratically
at the triple origin. The radius-independent constant comes from one fixed
physical ball. All integrability is derived from the original compact Hardy
bounds; no norm-scaling or inverse-distance integrability premise is supplied. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Metric
open scoped BigOperators
namespace ManyBody.S8
open TheoremT.Continuum

theorem physical_inverse_distance_budget_nonneg (x : Configuration 2) :
    0 ≤ physicalInverseDistanceBudget x :=
  Finset.sum_nonneg fun _ _ => inv_nonneg.mpr (norm_nonneg _)

theorem measurable_physical_inverse_distance_budget :
    Measurable physicalInverseDistanceBudget := by
  unfold physicalInverseDistanceBudget
  exact Finset.measurable_sum _ fun j _ =>
    (physicalDistanceLinearMaps j).continuous.measurable.norm.inv

theorem physical_inverse_distance_budget_smul {r : ℝ} (hr : 0 < r)
    (x : Configuration 2) :
    physicalInverseDistanceBudget (r • x) = r⁻¹ * physicalInverseDistanceBudget x := by
  unfold physicalInverseDistanceBudget
  simp only [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hr, mul_inv_rev]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem physical_closed_ball_inverse_dilation {r : ℝ} (hr : 0 < r)
    (x : Configuration 2) :
    x ∈ closedBall (0 : Configuration 2) (2*r) ↔
      r⁻¹ • x ∈ closedBall (0 : Configuration 2) 2 := by
  simp only [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hr)]
  rw [inv_mul_le_iff₀ hr]
  ring_nf

def physicalClosedBallDistanceBudgetClass (r : ℝ) :
    Lp ℝ 2 (volume : Measure (Configuration 2)) :=
  physicalDistanceCompactBudgetClass (closedBall 0 (2*r)) (isCompact_closedBall _ _)

theorem physical_closed_ball_distance_budget_L2_norm {r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) :
    ‖physicalClosedBallDistanceBudgetClass r‖ ≤
      r^2 * ‖physicalClosedBallDistanceBudgetClass 1‖ := by
  let g : Configuration 2 → ℝ :=
    (closedBall 0 2).indicator (fun x => 1+physicalInverseDistanceBudget x)
  have hg : MemLp g 2 volume :=
    physical_compact_inverse_distance_domination_memLp (isCompact_closedBall _ _)
  have hgm : Measurable g :=
    (measurable_const.add measurable_physical_inverse_distance_budget).indicator
      isClosed_closedBall.measurableSet
  have hgsq : Integrable (fun x => ‖g x‖^2) volume :=
    (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  have hdil : MemLp (fun x => g (r⁻¹ • x)) 2 volume :=
    (memLp_two_iff_integrable_sq_norm
      (hgm.comp (continuous_const_smul r⁻¹).measurable).aestronglyMeasurable).mpr
      (hgsq.comp_smul (inv_ne_zero hr.ne'))
  have hdim : Module.finrank ℝ (Configuration 2)=6 := by
    simp [Configuration, Coordinate, finrank_euclideanSpace, Fintype.card_prod]
  have hnormsq :
      ‖hdil.toLp (fun x => g (r⁻¹ • x))‖^2 =
        r^6 * ‖hg.toLp g‖^2 := by
    rw [actual_l2_toLp_norm_sq_integral hdil,
      Measure.integral_comp_inv_smul_of_nonneg volume (fun x => ‖g x‖^2) hr.le,
      hdim, smul_eq_mul, ← actual_l2_toLp_norm_sq_integral hg]
  have hnorm : ‖hdil.toLp (fun x => g (r⁻¹ • x))‖ =
      r^3 * ‖hg.toLp g‖ := by
    have hp : 0≤r^3*‖hg.toLp g‖ := by positivity
    have he : (r^3*‖hg.toLp g‖)^2=r^6*‖hg.toLp g‖^2 := by ring
    nlinarith [norm_nonneg (hdil.toLp (fun x => g (r⁻¹ • x)))]
  have hri : 1 ≤ r⁻¹ := (one_le_inv₀ hr).mpr hr1
  have hbound (x : Configuration 2) :
      ‖(closedBall (0 : Configuration 2) (2*r)).indicator
        (fun y => 1+physicalInverseDistanceBudget y) x‖ ≤ r⁻¹*‖g (r⁻¹ • x)‖ := by
    by_cases hx : x ∈ closedBall (0 : Configuration 2) (2*r)
    · have hy := (physical_closed_ball_inverse_dilation hr x).mp hx
      have hb := physical_inverse_distance_budget_nonneg x
      have hbi := physical_inverse_distance_budget_nonneg (r⁻¹ • x)
      simp only [Set.indicator_of_mem hx, g, Set.indicator_of_mem hy,
        Real.norm_eq_abs, abs_of_nonneg (by linarith : 0≤1+physicalInverseDistanceBudget x),
        abs_of_nonneg (by linarith : 0≤1+physicalInverseDistanceBudget (r⁻¹ • x))]
      rw [physical_inverse_distance_budget_smul (inv_pos.mpr hr), inv_inv]
      have hc : r⁻¹*r=1 := inv_mul_cancel₀ hr.ne'
      nlinarith
    · simp only [Set.indicator_of_notMem hx, norm_zero]
      positivity
  have h := Lp.norm_le_mul_norm_of_ae_le_mul
    (f:=physicalClosedBallDistanceBudgetClass r)
    (g:=hdil.toLp (fun x => g (r⁻¹ • x))) (c:=r⁻¹) (by
      filter_upwards [
        (physical_compact_inverse_distance_domination_memLp
          (isCompact_closedBall (0 : Configuration 2) (2*r))).coeFn_toLp,
        hdil.coeFn_toLp] with x hx hy
      change physicalClosedBallDistanceBudgetClass r x =
        (closedBall (0 : Configuration 2) (2*r)).indicator
          (fun y => 1+physicalInverseDistanceBudget y) x at hx
      rw [hx, hy]
      exact hbound x)
  have hgclass : hg.toLp g = physicalClosedBallDistanceBudgetClass 1 := by
    simp only [physicalClosedBallDistanceBudgetClass, physicalDistanceCompactBudgetClass, mul_one, g]
  rw [hnorm, hgclass] at h
  convert h using 1
  field_simp

theorem physical_two_electron_coulomb_abs_budget (Z : ℝ) (x : Configuration 2) :
    |coulombPotential 2 Z x| ≤ (|Z|+1)*physicalInverseDistanceBudget x := by
  rw [coulombPotential_two_electrons]
  have hb : physicalInverseDistanceBudget x =
      ‖position x 0‖⁻¹+‖position x 1‖⁻¹+‖position x 0-position x 1‖⁻¹ := by
    simp [physicalInverseDistanceBudget, Fin.sum_univ_three, physicalDistanceLinearMaps,
      electronPositionCLM_apply, pairDifferenceCLM_apply]
  rw [hb]
  have hn0 : 0≤‖position x 0‖⁻¹ := by positivity
  have hn1 : 0≤‖position x 1‖⁻¹ := by positivity
  have hp : 0≤‖position x 0-position x 1‖⁻¹ := by positivity
  calc
    _ ≤ |-Z*(‖position x 0‖⁻¹+‖position x 1‖⁻¹)|+
      |‖position x 0-position x 1‖⁻¹| := abs_add_le _ _
    _ = |Z| *(‖position x 0‖⁻¹+‖position x 1‖⁻¹)+
      ‖position x 0-position x 1‖⁻¹ := by
        rw [abs_mul, abs_neg, abs_of_nonneg (add_nonneg hn0 hn1), abs_of_nonneg hp]
    _ ≤ _ := by nlinarith [abs_nonneg Z]

theorem physical_closed_ball_coulomb_memLp (Z r : ℝ) :
    MemLp ((closedBall (0 : Configuration 2) (2*r)).indicator
      (coulombPotential 2 Z)) 2 volume := by
  have hb := physical_compact_inverse_distance_domination_memLp
    (isCompact_closedBall (0 : Configuration 2) (2*r))
  apply (hb.const_mul (|Z|+1)).norm.mono'
    ((measurable_coulombPotential 2 Z).indicator
      isClosed_closedBall.measurableSet).aestronglyMeasurable
  apply Eventually.of_forall
  intro x
  by_cases hx : x ∈ closedBall (0 : Configuration 2) (2*r)
  · simp only [Set.indicator_of_mem hx, norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0≤|Z|+1)]
    have hbi := physical_inverse_distance_budget_nonneg x
    rw [abs_of_nonneg (by linarith : 0≤1+physicalInverseDistanceBudget x)]
    exact (physical_two_electron_coulomb_abs_budget Z x).trans (by
      gcongr
      linarith)
  · simp [Set.indicator_of_notMem hx]

def physicalClosedBallCoulombClass (Z r : ℝ) :
    Lp ℝ 2 (volume : Measure (Configuration 2)) :=
  (physical_closed_ball_coulomb_memLp Z r).toLp
    ((closedBall (0 : Configuration 2) (2*r)).indicator (coulombPotential 2 Z))

theorem physical_closed_ball_coulomb_L2_norm (Z : ℝ) {r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) :
    ‖physicalClosedBallCoulombClass Z r‖ ≤
      ((|Z|+1)*‖physicalClosedBallDistanceBudgetClass 1‖)*r^2 := by
  have h : ‖physicalClosedBallCoulombClass Z r‖ ≤
      (|Z|+1)*‖physicalClosedBallDistanceBudgetClass r‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [(physical_closed_ball_coulomb_memLp Z r).coeFn_toLp,
      (physical_compact_inverse_distance_domination_memLp
        (isCompact_closedBall (0 : Configuration 2) (2*r))).coeFn_toLp] with x hx hy
    change physicalClosedBallCoulombClass Z r x = _ at hx
    change physicalClosedBallDistanceBudgetClass r x = _ at hy
    rw [hx,hy]
    by_cases hxm : x ∈ closedBall (0 : Configuration 2) (2*r)
    · simp only [Set.indicator_of_mem hxm, Real.norm_eq_abs]
      rw [abs_of_nonneg (by
        linarith [physical_inverse_distance_budget_nonneg x] :
          0≤1+physicalInverseDistanceBudget x)]
      exact (physical_two_electron_coulomb_abs_budget Z x).trans (by
        gcongr
        linarith)
    · simp [Set.indicator_of_notMem hxm]
  exact h.trans (by
    calc
      (|Z|+1)*‖physicalClosedBallDistanceBudgetClass r‖ ≤
          (|Z|+1)*(r^2*‖physicalClosedBallDistanceBudgetClass 1‖) :=
        mul_le_mul_of_nonneg_left (physical_closed_ball_distance_budget_L2_norm hr hr1)
          (by positivity)
      _ = _ := by ring)

theorem physical_closed_ball_coulomb_L2_norm_exact (Z : ℝ) {r : ℝ}
    (hr : 0 < r) :
    ‖physicalClosedBallCoulombClass Z r‖ =
      r^2 * ‖physicalClosedBallCoulombClass Z 1‖ := by
  let g : Configuration 2 → ℝ :=
    (closedBall 0 2).indicator (coulombPotential 2 Z)
  have hg : MemLp g 2 volume := by
    simpa only [mul_one] using physical_closed_ball_coulomb_memLp Z 1
  have hgr := physical_closed_ball_coulomb_memLp Z r
  have hfun :
      (fun x => ‖(closedBall (0 : Configuration 2) (2*r)).indicator
        (coulombPotential 2 Z) x‖^2) =
      (fun x => (r⁻¹)^2 * ‖g (r⁻¹ • x)‖^2) := by
    funext x
    by_cases hx : x ∈ closedBall (0 : Configuration 2) (2*r)
    · have hy := (physical_closed_ball_inverse_dilation hr x).mp hx
      simp only [Set.indicator_of_mem hx, g, Set.indicator_of_mem hy]
      rw [coulombPotential_eq_inv_dilated 2 Z hr x, norm_mul,
        Real.norm_eq_abs r⁻¹, abs_of_pos (inv_pos.mpr hr), mul_pow]
    · have hy : r⁻¹ • x ∉ closedBall (0 : Configuration 2) 2 :=
        fun hy => hx ((physical_closed_ball_inverse_dilation hr x).mpr hy)
      simp only [Set.indicator_of_notMem hx, g, Set.indicator_of_notMem hy,
        norm_zero, zero_pow (by decide : 2≠0), mul_zero]
  have hdim : Module.finrank ℝ (Configuration 2)=6 := by
    simp [Configuration, Coordinate, finrank_euclideanSpace, Fintype.card_prod]
  have hnormsq :
      ‖hgr.toLp ((closedBall (0 : Configuration 2) (2*r)).indicator
        (coulombPotential 2 Z))‖^2 = r^4 * ‖hg.toLp g‖^2 := by
    rw [actual_l2_toLp_norm_sq_integral hgr, hfun, integral_const_mul,
      Measure.integral_comp_inv_smul_of_nonneg volume (fun x => ‖g x‖^2) hr.le,
      hdim, smul_eq_mul, ← actual_l2_toLp_norm_sq_integral hg]
    field_simp
  have hgclass : hg.toLp g = physicalClosedBallCoulombClass Z 1 := by
    simp only [physicalClosedBallCoulombClass, mul_one, g]
  change ‖physicalClosedBallCoulombClass Z r‖^2 =
    r^4 * ‖hg.toLp g‖^2 at hnormsq
  rw [hgclass] at hnormsq
  have he : (r^2 * ‖physicalClosedBallCoulombClass Z 1‖)^2 =
      r^4 * ‖physicalClosedBallCoulombClass Z 1‖^2 := by ring
  have hp : 0≤r^2*‖physicalClosedBallCoulombClass Z 1‖ := by positivity
  nlinarith [norm_nonneg (physicalClosedBallCoulombClass Z r)]

theorem physical_compact_coulomb_quadratic_radius_budget (Z : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ r : ℝ, 0<r →
      ‖physicalClosedBallCoulombClass Z r‖≤C*r^2 := by
  refine ⟨‖physicalClosedBallCoulombClass Z 1‖, norm_nonneg _, ?_⟩
  intro r hr
  rw [physical_closed_ball_coulomb_L2_norm_exact Z hr, mul_comm]
theorem physical_ball_coulomb_memLp (Z r : ℝ) :
    MemLp ((ball (0 : Configuration 2) (2*r)).indicator
      (coulombPotential 2 Z)) 2 volume := by
  apply (physical_closed_ball_coulomb_memLp Z r).norm.mono'
    ((measurable_coulombPotential 2 Z).indicator isOpen_ball.measurableSet).aestronglyMeasurable
  apply Eventually.of_forall
  intro x
  by_cases hx : x ∈ ball (0 : Configuration 2) (2*r)
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (ball_subset_closedBall hx)]
  · simp only [Set.indicator_of_notMem hx, norm_zero]
    exact norm_nonneg _

def physicalBallCoulombClass (Z r : ℝ) :
    Lp ℝ 2 (volume : Measure (Configuration 2)) :=
  (physical_ball_coulomb_memLp Z r).toLp
    ((ball (0 : Configuration 2) (2*r)).indicator (coulombPotential 2 Z))

theorem physical_ball_coulomb_L2_norm (Z : ℝ) {r : ℝ} (hr : 0 < r) :
    ‖physicalBallCoulombClass Z r‖ ≤
      ‖physicalClosedBallCoulombClass Z 1‖*r^2 := by
  have h : ‖physicalBallCoulombClass Z r‖≤‖physicalClosedBallCoulombClass Z r‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [(physical_ball_coulomb_memLp Z r).coeFn_toLp,
      (physical_closed_ball_coulomb_memLp Z r).coeFn_toLp] with x hx hy
    change physicalBallCoulombClass Z r x = _ at hx
    change physicalClosedBallCoulombClass Z r x = _ at hy
    rw [hx,hy]
    by_cases hxm : x ∈ ball (0 : Configuration 2) (2*r)
    · rw [Set.indicator_of_mem hxm, Set.indicator_of_mem (ball_subset_closedBall hxm)]
    · simp only [Set.indicator_of_notMem hxm, norm_zero]
      exact norm_nonneg _
  exact h.trans (by rw [physical_closed_ball_coulomb_L2_norm_exact Z hr, mul_comm])
#print axioms physical_inverse_distance_budget_smul
#print axioms physical_closed_ball_distance_budget_L2_norm
#print axioms physical_closed_ball_coulomb_memLp
#print axioms physical_closed_ball_coulomb_L2_norm
#print axioms physical_closed_ball_coulomb_L2_norm_exact
#print axioms physical_compact_coulomb_quadratic_radius_budget
#print axioms physical_ball_coulomb_memLp
#print axioms physical_ball_coulomb_L2_norm
end ManyBody.S8
