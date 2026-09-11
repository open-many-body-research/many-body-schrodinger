import ContinuumFoundation_v1
import Mathlib.MeasureTheory.Function.Holder

/-!
Actual bounded frequency multiplier for the positive shift of -Delta/2.
The Fourier convention is exp(-2*pi*i*inner), so a(xi)=2*pi^2*norm(xi)^2.
The construction is a mathematical continuous linear operator on actual L2;
no executable numerical algorithm or computable Real representation is claimed.
-/

noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Filter
open scoped ENNReal

namespace TheoremT.Continuum

/-- Actual multiplication by an L-infinity symbol, using the existing
continuous bilinear Holder map L-infinity times L2 to L2. -/
def spatialL2BoundedMultiplier {N : ℕ} (m : Configuration N → ℂ)
    (hm : MemLp m ∞ volume) : SpatialL2 N →L[ℂ] SpatialL2 N :=
  (ContinuousLinearMap.lsmul ℂ ℂ).holderL volume ∞ 2 2 (hm.toLp m)

theorem spatialL2BoundedMultiplier_ae {N : ℕ} (m : Configuration N → ℂ)
    (hm : MemLp m ∞ volume) (f : SpatialL2 N) :
    spatialL2BoundedMultiplier m hm f =ᵐ[volume] fun x => m x * f x := by
  change (ContinuousLinearMap.lsmul ℂ ℂ).holder 2 (hm.toLp m) f =ᵐ[volume] _
  filter_upwards [(ContinuousLinearMap.lsmul ℂ ℂ).coeFn_holder (r := 2) (hm.toLp m) f,
    hm.coeFn_toLp] with x hx hm_x
  simpa only [hm_x, ContinuousLinearMap.lsmul_apply, smul_eq_mul] using hx

theorem norm_spatialL2BoundedMultiplier_apply_le {N : ℕ} (m : Configuration N → ℂ)
    (hm : MemLp m ∞ volume) {C : ℝ} (hC : ∀ x, ‖m x‖ ≤ C) (f : SpatialL2 N) :
    ‖spatialL2BoundedMultiplier m hm f‖ ≤ C * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [spatialL2BoundedMultiplier_ae m hm f] with x hx
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)

theorem norm_spatialL2BoundedMultiplier_le {N : ℕ} (m : Configuration N → ℂ)
    (hm : MemLp m ∞ volume) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x, ‖m x‖ ≤ C) :
    ‖spatialL2BoundedMultiplier m hm‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC0 (norm_spatialL2BoundedMultiplier_apply_le m hm hC)

def freeKineticSymbol (N : ℕ) (x : Configuration N) : ℝ :=
  (2 * Real.pi ^ 2) * ‖x‖ ^ 2

theorem freeKineticSymbol_nonneg (N : ℕ) (x : Configuration N) :
    0 ≤ freeKineticSymbol N x := by
  unfold freeKineticSymbol
  positivity

def freeResolventSymbol (N : ℕ) (μ : ℝ) (x : Configuration N) : ℂ :=
  ((freeKineticSymbol N x + μ)⁻¹ : ℝ)

theorem freeResolvent_denominator_pos (N : ℕ) {μ : ℝ} (hμ : 0 < μ)
    (x : Configuration N) : 0 < freeKineticSymbol N x + μ :=
  add_pos_of_nonneg_of_pos (freeKineticSymbol_nonneg N x) hμ

theorem freeResolventSymbol_continuous (N : ℕ) {μ : ℝ} (hμ : 0 < μ) :
    Continuous (freeResolventSymbol N μ) := by
  have ha : Continuous (fun x : Configuration N => freeKineticSymbol N x + μ) := by
    unfold freeKineticSymbol
    fun_prop
  exact Complex.continuous_ofReal.comp
    (ha.inv₀ (fun x => (freeResolvent_denominator_pos N hμ x).ne'))

theorem freeResolventSymbol_bound (N : ℕ) {μ : ℝ} (hμ : 0 < μ)
    (x : Configuration N) : ‖freeResolventSymbol N μ x‖ ≤ μ⁻¹ := by
  have hp := freeResolvent_denominator_pos N hμ x
  simp only [freeResolventSymbol, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hp)]
  simpa only [one_div] using
    one_div_le_one_div_of_le hμ (le_add_of_nonneg_left (freeKineticSymbol_nonneg N x))

theorem freeResolventSymbol_memLp_top (N : ℕ) {μ : ℝ} (hμ : 0 < μ) :
    MemLp (freeResolventSymbol N μ) ∞ volume :=
  memLp_top_of_bound (freeResolventSymbol_continuous N hμ).aestronglyMeasurable μ⁻¹
    (Eventually.of_forall (freeResolventSymbol_bound N hμ))

def freeResolventMultiplier (N : ℕ) (μ : ℝ) (hμ : 0 < μ) :
    SpatialL2 N →L[ℂ] SpatialL2 N :=
  spatialL2BoundedMultiplier (freeResolventSymbol N μ) (freeResolventSymbol_memLp_top N hμ)

theorem freeResolventMultiplier_ae (N : ℕ) {μ : ℝ} (hμ : 0 < μ) (f : SpatialL2 N) :
    freeResolventMultiplier N μ hμ f =ᵐ[volume]
      fun x => freeResolventSymbol N μ x * f x :=
  spatialL2BoundedMultiplier_ae _ _ f

theorem norm_freeResolventMultiplier_le (N : ℕ) {μ : ℝ} (hμ : 0 < μ) :
    ‖freeResolventMultiplier N μ hμ‖ ≤ μ⁻¹ :=
  norm_spatialL2BoundedMultiplier_le _ _ (inv_nonneg.mpr hμ.le)
    (freeResolventSymbol_bound N hμ)

theorem freeResolventSymbol_cancel (N : ℕ) {μ : ℝ} (hμ : 0 < μ)
    (x : Configuration N) :
    ((freeKineticSymbol N x + μ : ℝ) : ℂ) * freeResolventSymbol N μ x = 1 := by
  simp only [freeResolventSymbol, ← Complex.ofReal_mul]
  rw [mul_inv_cancel₀ (freeResolvent_denominator_pos N hμ x).ne']
  rfl

theorem freeKinetic_mul_resolvent_bound (N : ℕ) {μ : ℝ} (hμ : 0 < μ)
    (x : Configuration N) :
    ‖(freeKineticSymbol N x : ℂ) * freeResolventSymbol N μ x‖ ≤ 1 := by
  have hp := freeResolvent_denominator_pos N hμ x
  rw [norm_mul]
  simp only [freeResolventSymbol, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (freeKineticSymbol_nonneg N x), abs_of_pos (inv_pos.mpr hp)]
  rw [← div_eq_mul_inv]
  exact (div_le_one hp).mpr (le_add_of_nonneg_right hμ.le)

theorem freeKineticResolventSymbol_memLp_top (N : ℕ) {μ : ℝ} (hμ : 0 < μ) :
    MemLp (fun x : Configuration N =>
      (freeKineticSymbol N x : ℂ) * freeResolventSymbol N μ x) ∞ volume := by
  have ha : Continuous (fun x : Configuration N => (freeKineticSymbol N x : ℂ)) := by
    unfold freeKineticSymbol
    fun_prop
  exact memLp_top_of_bound (ha.mul (freeResolventSymbol_continuous N hμ)).aestronglyMeasurable 1
    (Eventually.of_forall (freeKinetic_mul_resolvent_bound N hμ))

/-- Bounded frequency multiplier with symbol a/(a+mu). -/
def freeKineticResolventMultiplier (N : ℕ) (μ : ℝ) (hμ : 0 < μ) :
    SpatialL2 N →L[ℂ] SpatialL2 N :=
  spatialL2BoundedMultiplier
    (fun x => (freeKineticSymbol N x : ℂ) * freeResolventSymbol N μ x)
    (freeKineticResolventSymbol_memLp_top N hμ)

theorem freeKineticResolventMultiplier_ae (N : ℕ) {μ : ℝ} (hμ : 0 < μ)
    (f : SpatialL2 N) :
    freeKineticResolventMultiplier N μ hμ f =ᵐ[volume]
      fun x => ((freeKineticSymbol N x : ℂ) * freeResolventSymbol N μ x) * f x :=
  spatialL2BoundedMultiplier_ae _ _ f

theorem norm_freeKineticResolventMultiplier_le (N : ℕ) {μ : ℝ} (hμ : 0 < μ) :
    ‖freeKineticResolventMultiplier N μ hμ‖ ≤ 1 :=
  norm_spatialL2BoundedMultiplier_le _ _ zero_le_one (freeKinetic_mul_resolvent_bound N hμ)

theorem freeResolventSymbol_partition (N : ℕ) {μ : ℝ} (hμ : 0 < μ)
    (x : Configuration N) :
    (freeKineticSymbol N x : ℂ) * freeResolventSymbol N μ x +
      (μ : ℂ) * freeResolventSymbol N μ x = 1 := by
  rw [← add_mul, ← Complex.ofReal_add]
  exact freeResolventSymbol_cancel N hμ x

#print axioms spatialL2BoundedMultiplier_ae
#print axioms norm_spatialL2BoundedMultiplier_le
#print axioms freeResolventMultiplier_ae
#print axioms norm_freeResolventMultiplier_le
#print axioms freeResolventSymbol_cancel
#print axioms freeKinetic_mul_resolvent_bound
#print axioms freeKineticResolventMultiplier_ae
#print axioms norm_freeKineticResolventMultiplier_le
#print axioms freeResolventSymbol_partition

end TheoremT.Continuum
