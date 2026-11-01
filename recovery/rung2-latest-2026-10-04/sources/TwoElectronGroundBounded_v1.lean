import CoulombEigenfunctionBounded_v1
import TwoElectronGroundH2Decay_v1

/-! A single actual normalized physical ground eigenfunction carries all the
proved symmetries, the global essential bound, and exponential H2 tails.
Its energy is the already identified bottom of the full fermionic spectrum. -/
noncomputable section
open MeasureTheory
namespace TheoremT.Continuum

theorem twoElectron_physical_ground_bounded_with_H2_decay (Z : ℝ) (hZ : 2 ≤ Z) :
    ∃ u : SpatialL2 2, ‖u‖ = 1 ∧ pullback twoElectronSwap u = u ∧ HasH2 u ∧
      scalarHamiltonianGraph 2 Z u (((variationalGroundEnergy 2 Z).toReal : ℂ) • u) ∧
      (∀ᵐ x, (u x).im = 0) ∧
      (∀ R : Position ≃ₗᵢ[ℝ] Position, spatialRotation 2 R u = u) ∧
      (∀ᵐ x, ‖u x‖ ≤ coulombMoserBoundCoefficient 2 Z (variationalGroundEnergy 2 Z).toReal) ∧
      ∃ d : Coordinate 2 → SpatialL2 2, ∃ e : Coordinate 2 → Coordinate 2 → SpatialL2 2,
        (∀ k, WeakPartial u (d k) k) ∧ (∀ k l, WeakPartial (d k) (e k l) l) ∧
        ∀ a : ℝ, 0 ≤ a → a^2 < Z^2/112 →
          ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, weakH2ExteriorNorm u d e r ≤ Real.exp (-a*r)*C := by
  obtain ⟨u,hu,hs,hH2,hg,hr,hrot,htail⟩ := twoElectron_physical_ground_with_H2_decay Z hZ
  refine ⟨u,hu,hs,hH2,hg,hr,hrot,?_,htail⟩
  simpa only [hu,mul_one] using scalar_coulomb_eigen_ae_bound (by norm_num : 0 < 2) hg

#print axioms twoElectron_physical_ground_bounded_with_H2_decay
end TheoremT.Continuum
