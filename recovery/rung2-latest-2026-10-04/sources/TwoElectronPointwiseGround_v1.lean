import TwoElectronGroundLipschitz_v1
import CoulombLipschitzPointBound_v1

/-! One actual normalized physical ground vector, its globally bounded locally
Lipschitz representative, pointwise symmetries, and genuine weak H2 tails. -/
noncomputable section
open MeasureTheory
namespace TheoremT.Continuum

theorem twoElectron_physical_pointwise_ground_with_H2_decay (Z : ℝ) (hZ : 2 ≤ Z) :
    ∃ f : SpatialL2 2, ∃ u : Configuration 2 → ℂ,
      ‖f‖=1 ∧ HasH2 f ∧
      scalarHamiltonianGraph 2 Z f (((variationalGroundEnergy 2 Z).toReal : ℂ) • f) ∧
      LocallyLipschitz u ∧ (f : Configuration 2 → ℂ) =ᵐ[volume] u ∧
      (∀ x, ‖u x‖ ≤ coulombMoserBoundCoefficient 2 Z (variationalGroundEnergy 2 Z).toReal) ∧
      (∀ x, (u x).im=0) ∧ (∀ x, u (permuteSpace twoElectronSwap x)=u x) ∧
      (∀ R : Position ≃ₗᵢ[ℝ] Position, ∀ x, u (configurationRotation 2 R x)=u x) ∧
      ∃ d : Coordinate 2 → SpatialL2 2, ∃ e : Coordinate 2 → Coordinate 2 → SpatialL2 2,
        (∀ k, WeakPartial f (d k) k) ∧ (∀ k l, WeakPartial (d k) (e k l) l) ∧
        ∀ a : ℝ, 0 ≤ a → a^2 < Z^2/112 →
          ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, weakH2ExteriorNorm f d e r ≤ Real.exp (-a*r)*C := by
  obtain ⟨f,u,hf,hH2,hg,hu,hEq,hr,hs,hrot,htail⟩ := twoElectron_physical_ground_locally_lipschitz Z hZ
  refine ⟨f,u,hf,hH2,hg,hu,hEq,?_,hr,hs,hrot,htail⟩
  simpa only [hf,mul_one] using scalar_coulomb_continuous_representative_bound
    (by norm_num : 0 < 2) hg hu.continuous hEq

#print axioms twoElectron_physical_pointwise_ground_with_H2_decay
end TheoremT.Continuum
