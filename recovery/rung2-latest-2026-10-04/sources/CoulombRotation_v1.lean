import CoulombIsometryCovariance_v1
import ConfigurationRotation_v1
import WeakPermutation_v2
import PotentialPermutation_v2

/-! Simultaneous physical rotations on the actual scalar Coulomb graph for
every finite electron count and real charge. -/
noncomputable section
open MeasureTheory
namespace TheoremT.Continuum

abbrev spatialRotation (N : ℕ) (R : Position ≃ₗᵢ[ℝ] Position) :
    SpatialL2 N →ₗᵢ[ℂ] SpatialL2 N :=
  configurationIsometryPull (configurationRotation N R)

theorem spatialRotation_pullback (N : ℕ) (R : Position ≃ₗᵢ[ℝ] Position)
    (π : Equiv.Perm (Fin N)) (f : SpatialL2 N) :
    spatialRotation N R (pullback π f) = pullback π (spatialRotation N R f) := by
  apply Lp.ext
  have h1 := (configurationRotation N R).measurePreserving.quasiMeasurePreserving.ae
    (pullback_coeFn_ae π f)
  have h2 := (permuteSpace π).measurePreserving.quasiMeasurePreserving.ae
    (configurationIsometryPull_ae (configurationRotation N R) f)
  filter_upwards [configurationIsometryPull_ae (configurationRotation N R) (pullback π f),
    pullback_coeFn_ae π (spatialRotation N R f),h1,h2] with x hx hy h1x h2x
  simp only [Function.comp_apply] at *
  rw [hx,hy,h1x,h2x,configurationRotation_permuteSpace]

theorem scalar_graph_spatialRotation {N : ℕ} {Z : ℝ}
    (R : Position ≃ₗᵢ[ℝ] Position) {f h : SpatialL2 N}
    (hg : scalarHamiltonianGraph N Z f h) :
    scalarHamiltonianGraph N Z (spatialRotation N R f) (spatialRotation N R h) :=
  scalar_graph_configurationIsometryPull (configurationRotation N R)
    (coulombPotential_configurationRotation N Z R) hg

theorem HasH2.spatialRotation {N : ℕ} {f : SpatialL2 N} (hf : HasH2 f)
    (R : Position ≃ₗᵢ[ℝ] Position) : HasH2 (spatialRotation N R f) :=
  hf.configurationIsometryPull (configurationRotation N R)

#print axioms spatialRotation_pullback
#print axioms scalar_graph_spatialRotation
end TheoremT.Continuum
