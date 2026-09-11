import TwoElectronPartialProjection_v1
import CommutingProjectionComparison_v1

/-! Discharge the projection-algebra premises with actual scalar coordinate maps.
Hydrogenic quadratic-form lower bounds remain explicit premises below. -/
noncomputable section
namespace TheoremT.Continuum

theorem twoElectron_jointProjection_norm_sq (f g : SpatialL2 1)
    (hf : ‖f‖ = 1) (hg : ‖g‖ = 1) (F : SpatialL2 2) :
    ‖twoElectronProjectFirst f (twoElectronProjectSecond g F)‖ ^ 2 =
      ‖inner ℂ (twoElectronTensor f g) F‖ ^ 2 := by
  rw [twoElectronProjectFirstSecond,norm_smul,twoElectronTensor_norm,hf,hg,mul_one,mul_one]

theorem twoElectron_projection_norm_sum (f g : SpatialL2 1)
    (hf : ‖f‖ = 1) (hg : ‖g‖ = 1) (F : SpatialL2 2) :
    ‖twoElectronProjectFirst f F‖ ^ 2 + ‖twoElectronProjectSecond g F‖ ^ 2 ≤
      ‖F‖ ^ 2 + ‖inner ℂ (twoElectronTensor f g) F‖ ^ 2 := by
  have h := OperatorTheory.commuting_projections_norm_square
    (twoElectronProjectFirst f).toLinearMap (twoElectronProjectSecond g).toLinearMap
    (twoElectronProjectFirst_isSymmetricProjection f hf)
    (twoElectronProjectSecond_isSymmetricProjection g hg) (twoElectronProject_commute f g) F
  change ‖twoElectronProjectFirst f F‖ ^ 2 + ‖twoElectronProjectSecond g F‖ ^ 2 ≤
    ‖F‖ ^ 2 + ‖twoElectronProjectFirst f (twoElectronProjectSecond g F)‖ ^ 2 at h
  rwa [twoElectron_jointProjection_norm_sq f g hf hg F] at h

theorem twoElectron_scalar_comparison_of_component_bounds (f g : SpatialL2 1)
    (hf : ‖f‖ = 1) (hg : ‖g‖ = 1) (F : SpatialL2 2) (Z e1 e2 e : ℝ)
    (h1 : -(Z^2/8) * ‖F‖^2 - (3*Z^2/8) * ‖twoElectronProjectFirst f F‖^2 ≤ e1)
    (h2 : -(Z^2/8) * ‖F‖^2 - (3*Z^2/8) * ‖twoElectronProjectSecond g F‖^2 ≤ e2)
    (he : e1+e2 ≤ e) :
    -(5*Z^2/8) * ‖F‖^2 ≤ e + (3*Z^2/8) * ‖inner ℂ (twoElectronTensor f g) F‖^2 := by
  have h := OperatorTheory.two_hydrogenic_comparisons_combine
    (twoElectronProjectFirst f).toLinearMap (twoElectronProjectSecond g).toLinearMap
    (twoElectronProjectFirst_isSymmetricProjection f hf)
    (twoElectronProjectSecond_isSymmetricProjection g hg) (twoElectronProject_commute f g)
    F Z e1 e2 e h1 h2 he
  change -(5*Z^2/8) * ‖F‖^2 ≤ e + (3*Z^2/8) *
    ‖twoElectronProjectFirst f (twoElectronProjectSecond g F)‖^2 at h
  rwa [twoElectron_jointProjection_norm_sq f g hf hg F] at h

#print axioms twoElectron_jointProjection_norm_sq
#print axioms twoElectron_projection_norm_sum
#print axioms twoElectron_scalar_comparison_of_component_bounds
end TheoremT.Continuum
