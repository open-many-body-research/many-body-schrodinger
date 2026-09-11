import PolarMeanIntegralSplits_v1
import PolarMeanTangential_v1

/-! Exact decomposition of the actual three-dimensional mass and Coulomb
quadratic form into the normalized half-line mean domain and the actual
physical fluctuation. No component-energy premise is assumed. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ContDiff Topology
namespace TheoremT.Polar

theorem physical_mean_fluctuation_mass {f : EnergyR3 → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (h0 : (0 : EnergyR3) ∉ tsupport f) :
    (∫ x : EnergyR3, ‖f x‖ ^ 2) =
      (4 * Real.pi) * ‖TheoremT.HalfLine.J (MeanProfile.meanDomain f hf hc h0)‖ ^ 2 +
      (∫ x : EnergyR3, ‖physicalFluctuation f x‖ ^ 2) := by
  rw [MeanProfile.meanDomain_norm_integral]
  exact physical_mean_fluctuation_mass_integral hf hc h0

theorem physical_mean_fluctuation_nuclear {f : EnergyR3 → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (h0 : (0 : EnergyR3) ∉ tsupport f) :
    (∫ x : EnergyR3, ‖f x‖ ^ 2 / ‖x‖) =
      (4 * Real.pi) * TheoremT.HalfLine.coulombMoment (MeanProfile.meanDomain f hf hc h0) +
      (∫ x : EnergyR3, ‖physicalFluctuation f x‖ ^ 2 / ‖x‖) := by
  rw [MeanProfile.meanDomain_nuclear_integral]
  exact physical_mean_fluctuation_nuclear_integral hf hc h0

theorem physical_fluctuation_angular_integral {f : EnergyR3 → ℂ}
    (hf : ContDiff ℝ ∞ f) (h0 : (0 : EnergyR3) ∉ tsupport f) :
    (∑ i : Fin 3, ∫ r : ℝ in Ioi 0, ∫ w : EnergySphere,
      ‖complexTangentialPartial i (fun y => physicalFluctuation f (r • y)) w.val‖ ^ 2
        ∂(volume : Measure EnergyR3).toSphere) =
      ∑ i : Fin 3, ∫ r : ℝ in Ioi 0, ∫ w : EnergySphere,
        ‖complexTangentialPartial i (fun y => f (r • y)) w.val‖ ^ 2
          ∂(volume : Measure EnergyR3).toSphere := by
  apply Finset.sum_congr rfl
  intro i _
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  apply integral_congr_ae
  apply Eventually.of_forall
  intro w
  dsimp only
  rw [physicalFluctuation_tangential_eq hf h0 w hr i]

theorem physical_mean_fluctuation_kinetic {f : EnergyR3 → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (h0 : (0 : EnergyR3) ∉ tsupport f) :
    (∫ x : EnergyR3, ∑ i : Fin 3, ‖fderiv ℝ f x (EuclideanSpace.single i 1)‖ ^ 2) =
      (4 * Real.pi) * ‖TheoremT.HalfLine.dJ (MeanProfile.meanDomain f hf hc h0)‖ ^ 2 +
      (∫ x : EnergyR3, ∑ i : Fin 3,
        ‖fderiv ℝ (physicalFluctuation f) x (EuclideanSpace.single i 1)‖ ^ 2) := by
  have hF := physicalFluctuation_contDiff hf h0
  have hFc := physicalFluctuation_compact hc
  rw [full_kinetic_polar_integral_separated hf hc,
    full_kinetic_polar_integral_separated hF hFc,
    physical_mean_fluctuation_radial_kinetic_integral hf hc h0,
    physical_fluctuation_angular_integral hf h0,
    MeanProfile.meanDomain_kinetic_integral]
  ring

theorem physical_mean_fluctuation_form {f : EnergyR3 → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (h0 : (0 : EnergyR3) ∉ tsupport f)
    (Z : ℝ) :
    (1 / 2) * (∫ x : EnergyR3, ∑ i : Fin 3,
      ‖fderiv ℝ f x (EuclideanSpace.single i 1)‖ ^ 2) -
      Z * (∫ x : EnergyR3, ‖f x‖ ^ 2 / ‖x‖) =
    (4 * Real.pi) * TheoremT.HalfLine.q Z (MeanProfile.meanDomain f hf hc h0) +
      ((1 / 2) * (∫ x : EnergyR3, ∑ i : Fin 3,
        ‖fderiv ℝ (physicalFluctuation f) x (EuclideanSpace.single i 1)‖ ^ 2) -
        Z * (∫ x : EnergyR3, ‖physicalFluctuation f x‖ ^ 2 / ‖x‖)) := by
  rw [physical_mean_fluctuation_kinetic hf hc h0,
    physical_mean_fluctuation_nuclear hf hc h0, TheoremT.HalfLine.q]
  ring

end TheoremT.Polar
