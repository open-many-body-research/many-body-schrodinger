import PolarMeanFormSplit_v1
import PolarMeanZeroSector_v1
import MeanSectorRankOne_v1

/-! Unconditional hydrogenic rank-one form comparison on the actual punctured
smooth compact core in Euclidean three-space. The angular and mean-sector
estimates and their exact form decomposition are all discharged dependencies. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff BigOperators
namespace TheoremT.Polar

theorem hydrogen_euclidean_core_rank_one (Z : ℝ) (hZ : 0 < Z)
    (f : EnergyR3 → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (h0 : (0 : EnergyR3) ∉ tsupport f) (g : Lp ℂ 2 (volume : Measure EnergyR3))
    (hg : (g : EnergyR3 → ℂ) =ᵐ[volume] f) :
    -(Z^2/8) * ‖g‖^2 - (3*Z^2/8) *
      ‖inner ℂ (normalizedPolarGround (by simp : Module.finrank ℝ EnergyR3 = 3) Z hZ) g‖^2 ≤
    (1/2) * (∫ x : EnergyR3, ∑ i : Fin 3,
      ‖fderiv ℝ f x (EuclideanSpace.single i 1)‖^2) -
      Z * (∫ x : EnergyR3, ‖f x‖^2 / ‖x‖) := by
  have hm := physical_mean_sector_rank_one
    (by simp : Module.finrank ℝ EnergyR3 = 3) Z hZ f hf hc h0 g hg
  have hfl := physicalFluctuation_energy_lower hf hc h0 Z
  have hform := physical_mean_fluctuation_form hf hc h0 Z
  rw [MeanProfile.meanDomain_q_integral] at hform
  have hn : ‖g‖^2 = ∫ x : EnergyR3, ‖f x‖^2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hg] with x hx
    rw [hx,real_inner_self_eq_norm_sq]
  rw [hn, physical_mean_fluctuation_mass_integral hf hc h0]
  have hh := add_le_add hm hfl
  rw [← hform] at hh
  nlinarith

#print axioms hydrogen_euclidean_core_rank_one
end TheoremT.Polar
