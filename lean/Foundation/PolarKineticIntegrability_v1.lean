import PolarThree_v1
import PolarKineticSplit_v1
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! Actual integrability prerequisites for three-dimensional polar kinetic
energy. Every integrability assertion is derived from smooth compact support
or from a proved weighted polar change of variables. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ContDiff Topology
namespace TheoremT.Polar

abbrev EnergyR3 := EuclideanSpace ℝ (Fin 3)
abbrev EnergySphere := Metric.sphere (0 : EnergyR3) 1

def fullKineticDensity (f : EnergyR3 → ℂ) (x : EnergyR3) : ℝ :=
  ∑ i : Fin 3, ‖fderiv ℝ f x (EuclideanSpace.single i 1)‖ ^ 2

theorem coordinate_kinetic_integrable {f : EnergyR3 → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (i : Fin 3) :
    Integrable (fun x => ‖fderiv ℝ f x (EuclideanSpace.single i 1)‖ ^ 2) := by
  have hd := (hf.continuous_fderiv (by simp)).clm_apply
    (continuous_const : Continuous (fun _ : EnergyR3 => EuclideanSpace.single i (1 : ℝ)))
  have hdc := hc.fderiv_apply ℝ (EuclideanSpace.single i 1)
  exact (hd.norm.pow 2).integrable_of_hasCompactSupport
    (by simpa only [pow_two] using (hdc.norm.mul_right : HasCompactSupport (fun x => ‖fderiv ℝ f x (EuclideanSpace.single i 1)‖ *
      ‖fderiv ℝ f x (EuclideanSpace.single i 1)‖)))

theorem fullKineticDensity_integrable {f : EnergyR3 → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    Integrable (fullKineticDensity f) := by
  exact integrable_finsetSum _ (fun i _ => coordinate_kinetic_integrable hf hc i)

theorem integrable_volumeIoiPow_iff_weighted (n : ℕ) (g : ℝ → ℝ) :
    Integrable (fun r : Ioi (0 : ℝ) => g r.val) (Measure.volumeIoiPow n) ↔
      IntegrableOn (fun r : ℝ => r ^ n * g r) (Ioi 0) := by
  rw [integrableOn_iff_comap_subtypeVal measurableSet_Ioi]
  rw [Measure.volumeIoiPow, integrable_withDensity_iff_integrable_smul']
  · apply integrable_congr
    apply Eventually.of_forall
    intro r
    simp only [Function.comp_def, smul_eq_mul]
    rw [ENNReal.toReal_ofReal (pow_nonneg r.property.le _)]
  · fun_prop
  · simp

theorem fullKineticDensity_polar_integrable {f : EnergyR3 → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    Integrable (fun p : EnergySphere × Ioi (0 : ℝ) =>
      fullKineticDensity f (p.2.val • p.1.val))
      ((volume : Measure EnergyR3).toSphere.prod (Measure.volumeIoiPow 2)) := by
  simpa using
    (integrable_polar_product_iff (volume : Measure EnergyR3) (fullKineticDensity f)).mp
      (fullKineticDensity_integrable hf hc)

end TheoremT.Polar
