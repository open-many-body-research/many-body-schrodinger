import PolarKineticComponents_v1

/-! Fubini for the actual radial kinetic density. The joint weighted
integrability has already been proved by domination by full kinetic energy. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ContDiff Topology
namespace TheoremT.Polar

theorem polarRadialKinetic_sphere_marginal_integrable {f : EnergyR3 → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    Integrable (fun w : EnergySphere => ∫ r : ℝ in Ioi 0,
      r ^ 2 * ‖fderiv ℝ f (r • w.val) w.val‖ ^ 2)
      (volume : Measure EnergyR3).toSphere := by
  have h := (polarRadialDensity_product_integrable hf hc).integral_prod_left
  apply h.congr
  apply Eventually.of_forall
  intro w
  simpa only [smul_eq_mul, polarRadialDensity] using
    integral_volumeIoiPow 2 (fun r => polarRadialDensity f r w)

theorem polarRadialKinetic_fubini {f : EnergyR3 → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    (∫ w : EnergySphere, (∫ r : ℝ in Ioi 0,
      r ^ 2 * ‖fderiv ℝ f (r • w.val) w.val‖ ^ 2)
      ∂(volume : Measure EnergyR3).toSphere) =
    ∫ r : ℝ in Ioi 0, r ^ 2 * (∫ w : EnergySphere,
      ‖fderiv ℝ f (r • w.val) w.val‖ ^ 2 ∂(volume : Measure EnergyR3).toSphere) := by
  calc
    _ = ∫ w : EnergySphere, (∫ r : Ioi (0 : ℝ), polarRadialDensity f r.val w
      ∂Measure.volumeIoiPow 2) ∂(volume : Measure EnergyR3).toSphere := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro w
      simpa only [smul_eq_mul, polarRadialDensity] using
        (integral_volumeIoiPow 2 (fun r => polarRadialDensity f r w)).symm
    _ = ∫ r : Ioi (0 : ℝ), (∫ w : EnergySphere, polarRadialDensity f r.val w
      ∂(volume : Measure EnergyR3).toSphere) ∂Measure.volumeIoiPow 2 :=
      integral_integral_swap (polarRadialDensity_product_integrable hf hc)
    _ = _ := by
      simpa only [smul_eq_mul, polarRadialDensity] using integral_volumeIoiPow 2
        (fun r => ∫ w : EnergySphere, polarRadialDensity f r w
          ∂(volume : Measure EnergyR3).toSphere)

end TheoremT.Polar
