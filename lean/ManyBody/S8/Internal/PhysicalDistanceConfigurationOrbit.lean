import ManyBody.S8.Internal.TwoVectorDistanceOrbit
import NuclearDistanceRealRepresentative_v1

/-! Exact simultaneous orthogonal reconstruction of actual two-electron
configurations from their three physical distances. The canonical real nuclear
representative covers all spectator-nonzero configurations, including nuclear
and collinear cases. No analytic representative or independent basis is assumed. -/
noncomputable section
namespace ManyBody.S8
open TheoremT.Continuum

theorem two_electron_configuration_rotation_of_distances
    (x y : Configuration 2)
    (h0 : ‖position x 0‖ = ‖position y 0‖)
    (h1 : ‖position x 1‖ = ‖position y 1‖)
    (hsep : ‖position x 0-position x 1‖ = ‖position y 0-position y 1‖) :
    ∃ Q : Position ≃ₗᵢ[ℝ] Position, configurationRotation 2 Q x = y := by
  obtain ⟨Q, hQ0, hQ1⟩ := two_vector_isometry_of_distances
    (position x 0) (position x 1) (position y 0) (position y 1) h0 h1 hsep
  refine ⟨Q, ?_⟩
  ext ⟨i,k⟩
  change (position (configurationRotation 2 Q x) i) k = (position y i) k
  rw [position_configurationRotation]
  fin_cases i
  · exact congrArg (fun p : Position => p k) hQ0
  · exact congrArg (fun p : Position => p k) hQ1

theorem rotation_invariant_eq_of_physical_distances
    (g : Configuration 2 → ℂ)
    (hg : ∀ Q : Position ≃ₗᵢ[ℝ] Position, ∀ x, g (configurationRotation 2 Q x) = g x)
    (x y : Configuration 2)
    (h0 : ‖position x 0‖ = ‖position y 0‖)
    (h1 : ‖position x 1‖ = ‖position y 1‖)
    (hsep : ‖position x 0-position x 1‖ = ‖position y 0-position y 1‖) : g x = g y := by
  obtain ⟨Q, hQ⟩ := two_electron_configuration_rotation_of_distances x y h0 h1 hsep
  have hh := hg Q x
  rw [hQ] at hh
  exact hh.symm

theorem nuclear_distance_real_representative_covers_original
    (x : Configuration 2) (hs : 0 < ‖position x 1‖) :
    ∃ Q : Position ≃ₗᵢ[ℝ] Position, configurationRotation 2 Q x =
      nuclearKSPhysicalCoordinates 0
        (nuclearDistanceRealSpatial ‖position x 0‖ ‖position x 1‖
          ‖position x 0-position x 1‖)
        (nuclearDistanceRealSpectator ‖position x 1‖) := by
  have hlo : |‖position x 0‖-‖position x 1‖| ≤ ‖position x 0-position x 1‖ :=
    abs_norm_sub_norm_le (position x 0) (position x 1)
  have hhi := norm_sub_le (position x 0) (position x 1)
  obtain ⟨h0,h1,hsep⟩ := nuclearDistanceRealRepresentative_configuration_norms
    (norm_nonneg (position x 0)) hs (norm_nonneg (position x 0-position x 1)) hlo hhi
  exact two_electron_configuration_rotation_of_distances x _ h0.symm h1.symm hsep.symm

theorem nuclear_distance_real_coordinates_rotation
    (i : Fin 2) (X T : Position) (hs : 0 < ‖T‖) :
    ∃ Q : Position ≃ₗᵢ[ℝ] Position,
      configurationRotation 2 Q (nuclearKSPhysicalCoordinates i X T) =
        nuclearKSPhysicalCoordinates i
          (nuclearDistanceRealSpatial ‖X‖ ‖T‖ ‖X-T‖)
          (nuclearDistanceRealSpectator ‖T‖) := by
  obtain ⟨hW,hX,hT,hsep⟩ := nuclearDistanceRealRepresentative_norms
    (norm_nonneg X) hs (norm_nonneg (X-T))
    (abs_norm_sub_norm_le X T) (norm_sub_le X T)
  obtain ⟨Q,hQX,hQT⟩ := two_vector_isometry_of_distances X T
    (nuclearDistanceRealSpatial ‖X‖ ‖T‖ ‖X-T‖)
    (nuclearDistanceRealSpectator ‖T‖) hX.symm hT.symm hsep.symm
  refine ⟨Q, ?_⟩
  rw [configurationRotation_nuclearKSPhysicalCoordinates, hQX, hQT]

theorem nuclear_rotation_invariant_eq_canonical_distances
    (g : Configuration 2 → ℂ)
    (hg : ∀ Q : Position ≃ₗᵢ[ℝ] Position, ∀ x, g (configurationRotation 2 Q x) = g x)
    (i : Fin 2) (X T : Position) (hs : 0 < ‖T‖) :
    g (nuclearKSPhysicalCoordinates i X T) =
      g (nuclearKSPhysicalCoordinates i
        (nuclearDistanceRealSpatial ‖X‖ ‖T‖ ‖X-T‖)
        (nuclearDistanceRealSpectator ‖T‖)) := by
  obtain ⟨Q,hQ⟩ := nuclear_distance_real_coordinates_rotation i X T hs
  have hh := hg Q (nuclearKSPhysicalCoordinates i X T)
  rw [hQ] at hh
  exact hh.symm

#print axioms two_electron_configuration_rotation_of_distances
#print axioms rotation_invariant_eq_of_physical_distances
#print axioms nuclear_distance_real_representative_covers_original
#print axioms nuclear_distance_real_coordinates_rotation
#print axioms nuclear_rotation_invariant_eq_canonical_distances
end ManyBody.S8
