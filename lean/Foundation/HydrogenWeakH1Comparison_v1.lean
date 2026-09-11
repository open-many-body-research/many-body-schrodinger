import HydrogenPhysicalCoreComparison_v1

/-! Actual weak-Sobolev hydrogen rank-one and complement inequalities on
the original physical continuum. Core density, Hardy control, radial/angular
estimates, normalization, and coordinate transport are proved dependencies. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace TheoremT.Continuum
open TheoremT.Polar

theorem hydrogen_weakH1_rank_one (Z : ℝ) (hZ : 0 < Z)
    (f : SpatialL2 1) (d : Coordinate 1 → SpatialL2 1)
    (hd : ∀ k, WeakPartial f (d k) k) :
    -(Z^2/8) * ‖f‖^2 ≤ (1/2 : ℝ) * (∑ k : Coordinate 1, ‖d k‖^2) -
      Z * (∫ x, ‖f x‖^2 / ‖x‖) +
      (3*Z^2/8) * ‖inner ℂ (normalizedPolarGround configuration_one_finrank Z hZ) f‖^2 := by
  exact punctured_core_integral_bound_extends_weakH1 Z (-(Z^2/8)) (3*Z^2/8)
    (innerSL ℂ (normalizedPolarGround configuration_one_finrank Z hZ))
    (fun u g dg hu hc h0 hg hdg => hydrogen_physical_core_rank_one Z hZ u g dg hu hc h0 hg hdg)
    f d hd

theorem hydrogen_weakH1_complement (Z : ℝ) (hZ : 0 < Z)
    (f : SpatialL2 1) (d : Coordinate 1 → SpatialL2 1)
    (hd : ∀ k, WeakPartial f (d k) k)
    (ho : inner ℂ (normalizedPolarGround configuration_one_finrank Z hZ) f = 0) :
    -(Z^2/8) * ‖f‖^2 ≤ (1/2 : ℝ) * (∑ k : Coordinate 1, ‖d k‖^2) -
      Z * (∫ x, ‖f x‖^2 / ‖x‖) := by
  simpa only [ho, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, add_zero]
    using hydrogen_weakH1_rank_one Z hZ f d hd

#print axioms hydrogen_weakH1_rank_one
#print axioms hydrogen_weakH1_complement
end TheoremT.Continuum
