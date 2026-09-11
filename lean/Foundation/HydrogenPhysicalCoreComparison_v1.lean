import HydrogenEuclideanCoreComparison_v1
import OneElectronGroundTransport_v1

/-! Hydrogenic comparison on the unchanged physical Configuration 1 core,
with actual L2 classes for the input and all three weak derivative values. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff BigOperators
namespace TheoremT.Continuum
open TheoremT.Polar TheoremT.HydrogenPolynomial

theorem hydrogen_physical_core_rank_one (Z : ℝ) (hZ : 0 < Z)
    (u : Configuration 1 → ℂ) (g : SpatialL2 1) (dg : Coordinate 1 → SpatialL2 1)
    (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) (h0 : (0 : Configuration 1) ∉ tsupport u)
    (hg : g =ᵐ[volume] u) (hdg : ∀ k, dg k =ᵐ[volume] smoothPartial u k) :
    -(Z^2/8) * ‖g‖^2 ≤ (1/2 : ℝ) * (∑ k : Coordinate 1, ‖dg k‖^2) -
      Z * (∫ x, ‖g x‖^2 / ‖x‖) +
      (3*Z^2/8) * ‖inner ℂ (normalizedPolarGround configuration_one_finrank Z hZ) g‖^2 := by
  have h := hydrogen_euclidean_core_rank_one Z hZ
    (fun x => u (oneElectronEuclidean.symm x)) (oneElectronEuclidean_contDiff hu)
    (oneElectronEuclidean_compact hc) (oneElectronEuclidean_punctured h0)
    (oneElectronL2ToEuclidean g) (oneElectronL2ToEuclidean_representative hg)
  rw [oneElectronL2ToEuclidean.norm_map, oneElectronL2_ground_inner,
    oneElectronEuclidean_kinetic_integral u (hu.differentiable (by simp)),
    oneElectronEuclidean_nuclear_integral] at h
  have hk : (∫ x : Configuration 1, ∑ k : Coordinate 1, ‖smoothPartial u k x‖^2) =
      ∑ k : Coordinate 1, ‖dg k‖^2 := by
    rw [integral_finset_sum Finset.univ (fun k _ => smooth_partial_sq_integrable hu hc k)]
    apply Finset.sum_congr rfl
    intro k _
    exact (spatialL2_norm_sq_representative (dg k) (smoothPartial u k) (hdg k)).symm
  have hn : (∫ x : Configuration 1, ‖u x‖^2 / ‖x‖) = ∫ x, ‖g x‖^2 / ‖x‖ := by
    apply integral_congr_ae
    filter_upwards [hg] with x hx
    rw [hx]
  rw [hk,hn] at h
  linarith

#print axioms hydrogen_physical_core_rank_one
end TheoremT.Continuum
