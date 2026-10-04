import NuclearDistanceRealRepresentative_v1

/-! Direct identification of the actual representative's transverse square
and longitudinal coordinate with the previously proved complex map. -/
noncomputable section
set_option autoImplicit false
namespace TheoremT.Continuum

theorem nuclearDistanceRealSpatial_transverse_square {r s u : ℝ}
    (hw : 0 ≤ nuclearDistanceRealW r s u) :
    (nuclearDistanceRealSpatial r s u 0)^2 + (nuclearDistanceRealSpatial r s u 1)^2 =
      nuclearDistanceRealW r s u := by
  simp [nuclearDistanceRealSpatial, Real.sq_sqrt hw]

theorem nuclearDistanceRealRepresentative_complex_axis {r s u : ℝ}
    (hw : 0 ≤ nuclearDistanceRealW r s u) :
    nuclearDistanceAxisMap ![(r : ℂ), (s : ℂ), (u : ℂ)] =
      ![(nuclearDistanceRealSpatial r s u 2 : ℂ),
        (nuclearDistanceRealSpatial r s u 0 : ℂ)^2 +
          (nuclearDistanceRealSpatial r s u 1 : ℂ)^2] := by
  ext i
  fin_cases i
  · simp [nuclearDistanceAxisMap, nuclearDistanceRealZ_complexification,
      nuclearDistanceRealSpatial]
  · change nuclearDistanceAxisW ![(r : ℂ), (s : ℂ), (u : ℂ)] =
      (nuclearDistanceRealSpatial r s u 0 : ℂ)^2 +
        (nuclearDistanceRealSpatial r s u 1 : ℂ)^2
    rw [nuclearDistanceRealW_complexification]
    exact_mod_cast (nuclearDistanceRealSpatial_transverse_square hw).symm

end TheoremT.Continuum
