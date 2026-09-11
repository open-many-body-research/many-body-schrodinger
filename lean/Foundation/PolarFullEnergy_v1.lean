import PolarKineticComponents_v1

/-! Full three-dimensional kinetic integral equals the actual radial and
angular kinetic integrals. All product, sphere, and radial integrability
obligations follow from actual smooth compact support in the imported proofs.
No origin exclusion is needed for this kinetic identity. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ContDiff Topology
namespace TheoremT.Polar

theorem scaled_tangential_sphere_integral {f : EnergyR3 → ℂ}
    (hf : ContDiff ℝ ∞ f) (r : ℝ) (i : Fin 3) :
    (∫ w : EnergySphere, ‖complexTangentialPartial i (fun y => f (r • y)) w.val‖ ^ 2
      ∂(volume : Measure EnergyR3).toSphere) =
    r ^ 2 * ∫ w : EnergySphere, polarTangentialDensity f i r w
      ∂(volume : Measure EnergyR3).toSphere := by
  simp_rw [complexTangentialPartial_scaled f (hf.differentiable (by simp)),
    norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  exact integral_const_mul _ _

theorem scaled_tangential_radial_integrable {f : EnergyR3 → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (i : Fin 3) :
    IntegrableOn (fun r : ℝ => ∫ w : EnergySphere,
      ‖complexTangentialPartial i (fun y => f (r • y)) w.val‖ ^ 2
        ∂(volume : Measure EnergyR3).toSphere) (Ioi 0) := by
  exact (polarTangentialEnergy_integrable hf hc i).congr
    (Eventually.of_forall (fun r => (scaled_tangential_sphere_integral hf r i).symm))

theorem full_polar_sphere_kinetic_split {f : EnergyR3 → ℂ}
    (hf : ContDiff ℝ ∞ f) (r : ℝ) :
    r ^ 2 * (∫ w : EnergySphere, fullKineticDensity f (r • w.val)
      ∂(volume : Measure EnergyR3).toSphere) =
    r ^ 2 * (∫ w : EnergySphere, ‖fderiv ℝ f (r • w.val) w.val‖ ^ 2
      ∂(volume : Measure EnergyR3).toSphere) +
    ∑ i : Fin 3, ∫ w : EnergySphere,
      ‖complexTangentialPartial i (fun y => f (r • y)) w.val‖ ^ 2
        ∂(volume : Measure EnergyR3).toSphere := by
  simp_rw [fullKineticDensity_polar_split]
  rw [integral_add (polarRadialDensity_sphere_integrable hf r)
    (integrable_finsetSum _ (fun i _ => polarTangentialDensity_sphere_integrable hf r i))]
  rw [integral_finsetSum _ (fun i _ => polarTangentialDensity_sphere_integrable hf r i),
    mul_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact (scaled_tangential_sphere_integral hf r i).symm

theorem full_polar_energy_integrable {f : EnergyR3 → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    IntegrableOn (fun r : ℝ =>
      r ^ 2 * (∫ w : EnergySphere, ‖fderiv ℝ f (r • w.val) w.val‖ ^ 2
        ∂(volume : Measure EnergyR3).toSphere) +
      ∑ i : Fin 3, ∫ w : EnergySphere,
        ‖complexTangentialPartial i (fun y => f (r • y)) w.val‖ ^ 2
          ∂(volume : Measure EnergyR3).toSphere) (Ioi 0) :=
  (polarRadialEnergy_integrable hf hc).add
    (integrable_finsetSum _ (fun i _ => scaled_tangential_radial_integrable hf hc i))

theorem full_kinetic_polar_integral {f : EnergyR3 → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    (∫ x : EnergyR3, ∑ i : Fin 3,
      ‖fderiv ℝ f x (EuclideanSpace.single i 1)‖ ^ 2) =
    ∫ r : ℝ in Ioi 0,
      (r ^ 2 * (∫ w : EnergySphere, ‖fderiv ℝ f (r • w.val) w.val‖ ^ 2
        ∂(volume : Measure EnergyR3).toSphere) +
      ∑ i : Fin 3, ∫ w : EnergySphere,
        ‖complexTangentialPartial i (fun y => f (r • y)) w.val‖ ^ 2
          ∂(volume : Measure EnergyR3).toSphere) := by
  calc
    (∫ x : EnergyR3, fullKineticDensity f x) = ∫ r : ℝ in Ioi 0,
      r ^ 2 * ∫ w : EnergySphere, fullKineticDensity f (r • w.val)
        ∂(volume : Measure EnergyR3).toSphere := by
      simpa only [smul_eq_mul] using integral_polar_dim_three_radius_outer
        (by simp : Module.finrank ℝ EnergyR3 = 3) (fullKineticDensity f)
        (fullKineticDensity_integrable hf hc)
    _ = _ := setIntegral_congr_fun measurableSet_Ioi (fun r _ =>
      full_polar_sphere_kinetic_split hf r)

theorem full_kinetic_polar_integral_separated {f : EnergyR3 → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    (∫ x : EnergyR3, ∑ i : Fin 3,
      ‖fderiv ℝ f x (EuclideanSpace.single i 1)‖ ^ 2) =
    (∫ r : ℝ in Ioi 0, r ^ 2 *
      ∫ w : EnergySphere, ‖fderiv ℝ f (r • w.val) w.val‖ ^ 2
        ∂(volume : Measure EnergyR3).toSphere) +
    ∑ i : Fin 3, ∫ r : ℝ in Ioi 0, ∫ w : EnergySphere,
      ‖complexTangentialPartial i (fun y => f (r • y)) w.val‖ ^ 2
        ∂(volume : Measure EnergyR3).toSphere := by
  have hr := polarRadialEnergy_integrable hf hc
  dsimp only [polarRadialDensity] at hr
  rw [full_kinetic_polar_integral hf hc,
    integral_add hr
      (integrable_finsetSum Finset.univ (fun i _ => scaled_tangential_radial_integrable hf hc i)),
    integral_finsetSum Finset.univ (fun i _ => scaled_tangential_radial_integrable hf hc i)]

end TheoremT.Polar
