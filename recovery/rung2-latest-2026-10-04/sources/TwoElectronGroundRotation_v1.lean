import HydrogenProductRotation_v1
import TwoElectronSpatialOverlap_v1
import TwoElectronGroundReal_v1

/-! Every symmetric spatial eigenvector below the physical comparison separator
is fixed by simultaneous orthogonal transformations. In particular the actual
real spatial ground eigenfunction has exact rotation invariance in L². -/
noncomputable section
open MeasureTheory
namespace TheoremT.Continuum
open TheoremT.Polar

theorem symmetric_low_eigen_spatialRotation (Z : ℝ) (hZ : 0 < Z)
    {f : SpatialL2 2} (hs : pullback twoElectronSwap f = f)
    (E : ℝ) (hE : E < -(5*Z^2/8))
    (hg : scalarHamiltonianGraph 2 Z f ((E : ℂ) • f))
    (R : Position ≃ₗᵢ[ℝ] Position) : spatialRotation 2 R f = f := by
  apply symmetric_low_eigen_eq_of_product_overlap_eq Z hZ
    (by rw [← spatialRotation_pullback,hs]) hs E hE
  · have h := scalar_graph_spatialRotation R hg
    rwa [map_smul] at h
  · exact hg
  · have h := (spatialRotation 2 R).inner_map_map
      (twoElectronTensor (normalizedPolarGround configuration_one_finrank Z hZ)
        (normalizedPolarGround configuration_one_finrank Z hZ)) f
    rwa [hydrogenProduct_spatialRotation] at h

theorem twoElectron_ground_real_rotation_invariant (Z : ℝ) (hZ : 0 < Z)
    (hsep : 32 < 9*Z^2) :
    ∃ u : SpatialL2 2, ‖u‖ = 1 ∧ pullback twoElectronSwap u = u ∧ HasH2 u ∧
      scalarHamiltonianGraph 2 Z u (((variationalGroundEnergy 2 Z).toReal : ℂ) • u) ∧
      (∀ᵐ x, (u x).im = 0) ∧
      ∀ R : Position ≃ₗᵢ[ℝ] Position, spatialRotation 2 R u = u := by
  obtain ⟨u,hu,hs,hH2,hg,hr⟩ := twoElectron_ground_real_spatial_eigenfunction Z hZ hsep
  refine ⟨u,hu,hs,hH2,hg,hr,fun R => ?_⟩
  exact symmetric_low_eigen_spatialRotation Z hZ hs _
    (twoElectron_physical_ground_branch Z hZ hsep).1 hg R

#print axioms symmetric_low_eigen_spatialRotation
#print axioms twoElectron_ground_real_rotation_invariant
end TheoremT.Continuum
