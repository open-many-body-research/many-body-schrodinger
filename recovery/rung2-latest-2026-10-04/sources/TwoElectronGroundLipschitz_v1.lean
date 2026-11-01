import CoulombLocallyLipschitz_v1
import TwoElectronGroundBounded_v1
import ContinuousRepresentativeSymmetry_v1

/-! A single physical ground vector and a pointwise, globally defined locally
Lipschitz representative carrying exact exchange/rotation/real symmetries. -/
noncomputable section
open MeasureTheory
namespace TheoremT.Continuum

theorem twoElectron_physical_ground_locally_lipschitz (Z : ℝ) (hZ : 2 ≤ Z) :
    ∃ f : SpatialL2 2, ∃ u : Configuration 2 → ℂ,
      ‖f‖=1 ∧ HasH2 f ∧
      scalarHamiltonianGraph 2 Z f (((variationalGroundEnergy 2 Z).toReal : ℂ) • f) ∧
      LocallyLipschitz u ∧ (f : Configuration 2 → ℂ) =ᵐ[volume] u ∧
      (∀ x, (u x).im=0) ∧ (∀ x, u (permuteSpace twoElectronSwap x)=u x) ∧
      (∀ R : Position ≃ₗᵢ[ℝ] Position, ∀ x, u (configurationRotation 2 R x)=u x) ∧
      ∃ d : Coordinate 2 → SpatialL2 2, ∃ e : Coordinate 2 → Coordinate 2 → SpatialL2 2,
        (∀ k, WeakPartial f (d k) k) ∧ (∀ k l, WeakPartial (d k) (e k l) l) ∧
        ∀ a : ℝ, 0 ≤ a → a^2 < Z^2/112 →
          ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, weakH2ExteriorNorm f d e r ≤ Real.exp (-a*r)*C := by
  obtain ⟨f,hf,hs,hH2,hg,hr,hrot,hbound,htail⟩ := twoElectron_physical_ground_bounded_with_H2_decay Z hZ
  obtain ⟨u,hu,hEq⟩ := scalar_coulomb_locally_lipschitz_representative (by norm_num : 0 < 2) hg
  refine ⟨f,u,hf,hH2,hg,hu,hEq,continuous_representative_real hu.continuous hEq hr,?_,?_,htail⟩
  · apply continuous_representative_invariant hu.continuous hEq
    have he := pullback_ae twoElectronSwap f
    rwa [hs] at he
  · intro R
    apply continuous_representative_invariant hu.continuous hEq
    have he := configurationIsometryPull_ae (configurationRotation 2 R) f
    change (spatialRotation 2 R f : Configuration 2 → ℂ) =ᵐ[volume] _ at he
    rwa [hrot R] at he

#print axioms twoElectron_physical_ground_locally_lipschitz
end TheoremT.Continuum
