import NuclearDistanceAxisAlgebra_v1
import PhysicalKSCoordinatesRotation_v1

/-! A literal real planar representative of a physical distance triple,
including collinear configurations and the nuclear collision. The real
square root constructs a point only; no analytic square-root coordinate
or area division is asserted. -/
noncomputable section
set_option autoImplicit false
namespace TheoremT.Continuum

def nuclearDistanceRealZ (r s u : ℝ) : ℝ := (r^2 + s^2 - u^2) / (2 * s)

def nuclearDistanceRealW (r s u : ℝ) : ℝ := r^2 - (nuclearDistanceRealZ r s u)^2

def nuclearDistanceRealSpatial (r s u : ℝ) : Position :=
  WithLp.toLp 2 ![Real.sqrt (nuclearDistanceRealW r s u), 0, nuclearDistanceRealZ r s u]

def nuclearDistanceRealSpectator (s : ℝ) : Position := WithLp.toLp 2 ![0, 0, s]

theorem nuclearDistanceRealZ_complexification (r s u : ℝ) :
    nuclearDistanceAxisZ ![(r : ℂ), (s : ℂ), (u : ℂ)] = (nuclearDistanceRealZ r s u : ℂ) := by
  simp [nuclearDistanceAxisZ, nuclearDistanceRealZ]

theorem nuclearDistanceRealW_complexification (r s u : ℝ) :
    nuclearDistanceAxisW ![(r : ℂ), (s : ℂ), (u : ℂ)] = (nuclearDistanceRealW r s u : ℂ) := by
  simp [nuclearDistanceAxisW, nuclearDistanceRealW, nuclearDistanceRealZ_complexification]

theorem nuclearDistanceReal_heron (r s u : ℝ) (hs : s ≠ 0) :
    4 * s^2 * nuclearDistanceRealW r s u =
      ((r + s)^2 - u^2) * (u^2 - (r - s)^2) := by
  unfold nuclearDistanceRealW nuclearDistanceRealZ
  field_simp
  ring

theorem nuclearDistanceRealW_nonneg {r s u : ℝ} (hr : 0 ≤ r) (hs : 0 < s)
    (hu : 0 ≤ u) (hlo : |r - s| ≤ u) (hhi : u ≤ r + s) :
    0 ≤ nuclearDistanceRealW r s u := by
  have hleft : 0 ≤ (r + s)^2 - u^2 := by
    have hh := (sq_le_sq₀ hu (by linarith : 0 ≤ r + s)).mpr hhi
    linarith
  have hright : 0 ≤ u^2 - (r - s)^2 := by
    have hh := (sq_le_sq₀ (abs_nonneg (r - s)) hu).mpr hlo
    rw [sq_abs] at hh
    linarith
  have h := mul_nonneg hleft hright
  rw [← nuclearDistanceReal_heron r s u hs.ne'] at h
  exact nonneg_of_mul_nonneg_right h (by positivity : 0 < 4 * s^2)

theorem nuclearDistanceReal_shifted_square (r s u : ℝ) (hs : s ≠ 0) :
    nuclearDistanceRealW r s u + (nuclearDistanceRealZ r s u - s)^2 = u^2 := by
  unfold nuclearDistanceRealW nuclearDistanceRealZ
  field_simp
  ring

theorem nuclearDistanceRealSpatial_norm {r s u : ℝ} (hr : 0 ≤ r)
    (hw : 0 ≤ nuclearDistanceRealW r s u) : ‖nuclearDistanceRealSpatial r s u‖ = r := by
  apply (sq_eq_sq₀ (norm_nonneg _) hr).mp
  simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, nuclearDistanceRealSpatial,
    Real.sq_sqrt hw]
  simp [nuclearDistanceRealW]

theorem nuclearDistanceRealSpectator_norm {s : ℝ} (hs : 0 ≤ s) :
    ‖nuclearDistanceRealSpectator s‖ = s := by
  apply (sq_eq_sq₀ (norm_nonneg _) hs).mp
  simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, nuclearDistanceRealSpectator]

theorem nuclearDistanceReal_separation_norm {r s u : ℝ} (hs : s ≠ 0) (hu : 0 ≤ u)
    (hw : 0 ≤ nuclearDistanceRealW r s u) :
    ‖nuclearDistanceRealSpatial r s u - nuclearDistanceRealSpectator s‖ = u := by
  apply (sq_eq_sq₀ (norm_nonneg _) hu).mp
  simpa [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, nuclearDistanceRealSpatial,
    nuclearDistanceRealSpectator, Real.sq_sqrt hw] using nuclearDistanceReal_shifted_square r s u hs

theorem nuclearDistanceRealRepresentative_norms {r s u : ℝ} (hr : 0 ≤ r) (hs : 0 < s)
    (hu : 0 ≤ u) (hlo : |r - s| ≤ u) (hhi : u ≤ r + s) :
    0 ≤ nuclearDistanceRealW r s u ∧
      ‖nuclearDistanceRealSpatial r s u‖ = r ∧ ‖nuclearDistanceRealSpectator s‖ = s ∧
      ‖nuclearDistanceRealSpatial r s u - nuclearDistanceRealSpectator s‖ = u := by
  have hw := nuclearDistanceRealW_nonneg hr hs hu hlo hhi
  exact ⟨hw, nuclearDistanceRealSpatial_norm hr hw, nuclearDistanceRealSpectator_norm hs.le,
    nuclearDistanceReal_separation_norm hs.ne' hu hw⟩

theorem nuclearDistanceRealRepresentative_configuration_norms {r s u : ℝ}
    (hr : 0 ≤ r) (hs : 0 < s) (hu : 0 ≤ u) (hlo : |r - s| ≤ u) (hhi : u ≤ r + s) :
    let q := nuclearKSPhysicalCoordinates 0 (nuclearDistanceRealSpatial r s u)
      (nuclearDistanceRealSpectator s)
    ‖position q 0‖ = r ∧ ‖position q 1‖ = s ∧ ‖position q 0 - position q 1‖ = u := by
  simpa [position_nuclearKSPhysicalCoordinates] using
    (nuclearDistanceRealRepresentative_norms hr hs hu hlo hhi).2

end TheoremT.Continuum
