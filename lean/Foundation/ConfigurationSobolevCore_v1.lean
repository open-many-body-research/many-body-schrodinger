import ConfigurationDerivativeNorm_v1
import HardyLaplacianCore_v1
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality

/-! The compact smooth Sobolev inequality with the project's actual coordinate
derivatives. The finite constant is Mathlib's Haar-measure constant; no explicit
numerical evaluation or bit-computability of that constant is asserted. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff NNReal ENNReal
namespace TheoremT.Continuum
set_option maxHeartbeats 800000

def configurationSobolevConstant (N : ℕ) : ℝ≥0 :=
  eLpNormLESNormFDerivOfEqInnerConst (volume : Measure (Configuration N)) 2

theorem configuration_fderiv_L2_le_sum {N : ℕ} {u : Configuration N → ℂ}
    (hu : ContDiff ℝ ∞ u) :
    eLpNorm (fderiv ℝ u) 2 volume ≤
      ∑ k : Coordinate N, eLpNorm (smoothPartial u k) 2 volume := by
  classical
  calc
    eLpNorm (fderiv ℝ u) 2 volume ≤
        eLpNorm (fun x => ∑ k : Coordinate N, ‖smoothPartial u k x‖) 2 volume := by
      apply eLpNorm_mono_ae
      exact Filter.Eventually.of_forall (fun x => by
        simpa only [Real.norm_eq_abs,abs_of_nonneg (Finset.sum_nonneg
          (fun k _ => norm_nonneg _)),smoothPartial] using
          configuration_clm_norm_le_sum N (fderiv ℝ u x))
    _ ≤ ∑ k : Coordinate N, eLpNorm (fun x => ‖smoothPartial u k x‖) 2 volume := by
      have he : (∑ k : Coordinate N, fun x => ‖smoothPartial u k x‖) =
          (fun x => ∑ k : Coordinate N, ‖smoothPartial u k x‖) := by ext x; simp
      simpa only [he] using eLpNorm_sum_le
        (μ := volume) (s := Finset.univ) (f := fun k x => ‖smoothPartial u k x‖)
        (fun k _ => (smoothPartial_contDiff hu k).continuous.norm.aestronglyMeasurable)
        (show (1 : ℝ≥0∞) ≤ 2 by norm_num)
    _ = _ := by simp only [eLpNorm_norm]

theorem configuration_sobolev_core {N : ℕ} {u : Configuration N → ℂ}
    (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u)
    {q : ℝ≥0} (hN : 0 < Module.finrank ℝ (Configuration N))
    (hq : (q : ℝ)⁻¹ = (2 : ℝ)⁻¹ -
      (Module.finrank ℝ (Configuration N) : ℝ)⁻¹) :
    eLpNorm u q volume ≤ (configurationSobolevConstant N : ℝ≥0∞) *
      ∑ k : Coordinate N, eLpNorm (smoothPartial u k) 2 volume := by
  exact (eLpNorm_le_eLpNorm_fderiv_of_eq_inner volume
    (hu.of_le (by simp)) hc (p := 2) (by norm_num) hN hq).trans
      (mul_le_mul le_rfl (configuration_fderiv_L2_le_sum hu) (by positivity) (by positivity))

#print axioms configuration_fderiv_L2_le_sum
#print axioms configuration_sobolev_core
end TheoremT.Continuum
