import HardyLaplacianL2Core_v1
import HardyWeakCore_v1
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-! Actual compact smooth dilation in the original configuration-space L² and
weak Sobolev domains. No variational or spectral bound is assumed. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace TheoremT.Continuum

def spatialDilation {N : ℕ} (R : ℝ) (u : Configuration N → ℂ) :
    Configuration N → ℂ := fun x => u (R⁻¹ • x)

theorem spatialDilation_contDiff {N : ℕ} {u : Configuration N → ℂ}
    (hu : ContDiff ℝ ∞ u) (R : ℝ) : ContDiff ℝ ∞ (spatialDilation R u) :=
  hu.comp (contDiff_id.const_smul R⁻¹)

theorem spatialDilation_compact {N : ℕ} {u : Configuration N → ℂ}
    (hc : HasCompactSupport u) {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (spatialDilation R u) := by
  exact hc.comp_homeomorph (Homeomorph.smul (Units.mk0 R⁻¹ (inv_ne_zero hR.ne')))

theorem spatialDilation_partial {N : ℕ} (u : Configuration N → ℂ)
    (R : ℝ) (k : Coordinate N) (x : Configuration N) :
    smoothPartial (spatialDilation R u) k x =
      R⁻¹ • smoothPartial u k (R⁻¹ • x) := by
  change fderiv ℝ (fun y => u (R⁻¹ • y)) x (coordinateVector k) = _
  rw [fderiv_comp_smul]
  rfl

def smoothCoreL2 {N : ℕ} {u : Configuration N → ℂ}
    (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) : SpatialL2 N :=
  (hu.continuous.memLp_of_hasCompactSupport (p := 2) hc).toLp u

theorem smoothCoreL2_ae {N : ℕ} {u : Configuration N → ℂ}
    (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) :
    (smoothCoreL2 hu hc : Configuration N → ℂ) =ᵐ[volume] u :=
  MemLp.coeFn_toLp _

theorem smoothCoreL2_norm_sq {N : ℕ} {u : Configuration N → ℂ}
    (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) :
    ‖smoothCoreL2 hu hc‖^2 = ∫ x, ‖u x‖^2 := by
  rw [spatialL2_norm_sq_eq_integral]
  exact integral_congr_ae ((smoothCoreL2_ae hu hc).fun_comp (fun z : ℂ => ‖z‖^2))

theorem smoothCoreL2_hasH2 {N : ℕ} {u : Configuration N → ℂ}
    (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) :
    HasH2 (smoothCoreL2 hu hc) :=
  compact_c2_hasH2 (hu.of_le (by simp)) hc _

theorem smoothCoreL2_weakPartial {N : ℕ} {u : Configuration N → ℂ}
    (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) (k : Coordinate N) :
    WeakPartial (smoothCoreL2 hu hc)
      (smoothCoreL2 (smoothPartial_contDiff hu k) (smoothPartial_compact hc k)) k :=
  classicalDerivative_to_WeakPartial (hu.of_le (by simp)) k _ _

theorem spatialDilation_norm_sq {N : ℕ} {u : Configuration N → ℂ}
    (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) {R : ℝ} (hR : 0 < R) :
    ‖smoothCoreL2 (spatialDilation_contDiff hu R) (spatialDilation_compact hc hR)‖^2 =
      R ^ Module.finrank ℝ (Configuration N) * ‖smoothCoreL2 hu hc‖^2 := by
  rw [smoothCoreL2_norm_sq, smoothCoreL2_norm_sq]
  exact Measure.integral_comp_inv_smul_of_nonneg volume (fun x => ‖u x‖^2) hR.le

theorem spatialDilation_partial_norm_sq {N : ℕ} {u : Configuration N → ℂ}
    (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) {R : ℝ} (hR : 0 < R)
    (k : Coordinate N) :
    ‖smoothCoreL2 (smoothPartial_contDiff (spatialDilation_contDiff hu R) k)
      (smoothPartial_compact (spatialDilation_compact hc hR) k)‖^2 =
      (R⁻¹)^2 * R ^ Module.finrank ℝ (Configuration N) *
        ‖smoothCoreL2 (smoothPartial_contDiff hu k) (smoothPartial_compact hc k)‖^2 := by
  rw [smoothCoreL2_norm_sq, smoothCoreL2_norm_sq]
  simp_rw [spatialDilation_partial, norm_smul, Real.norm_eq_abs, mul_pow,
    sq_abs]
  rw [integral_const_mul,
    Measure.integral_comp_inv_smul_of_nonneg volume
      (fun x => ‖smoothPartial u k x‖^2) hR.le]
  simp only [smul_eq_mul, mul_assoc]

#print axioms spatialDilation_partial
#print axioms smoothCoreL2_hasH2
#print axioms smoothCoreL2_weakPartial
#print axioms spatialDilation_norm_sq
#print axioms spatialDilation_partial_norm_sq
end TheoremT.Continuum
