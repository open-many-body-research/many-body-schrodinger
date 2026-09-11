import PolarBochner_v1
import HydrogenRadialNorm_v1

/-! Exact three-dimensional polar normalization for canonical Euclidean volume.
The angular measure is the area measure with mass 4π, not probability measure.
Specializations include both Euclidean Fin 3 and the actual Configuration 1. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace TheoremT.Polar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem unit_ball_volume_real_dim_three (hdim : Module.finrank ℝ E = 3) :
    (volume : Measure E).real (Metric.ball 0 1) = Real.pi * 4 / 3 := by
  rw [Measure.real, InnerProductSpace.volume_ball_of_dim_odd (k := 1) (by simpa using hdim)]
  norm_num [hdim, ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi * 4 / 3)]

theorem sphere_volume_real_dim_three (hdim : Module.finrank ℝ E = 3) :
    (volume : Measure E).toSphere.real univ = 4 * Real.pi := by
  rw [Measure.toSphere_real_apply_univ, hdim, unit_ball_volume_real_dim_three hdim]
  norm_num
  ring

theorem sphere_volume_dim_three (hdim : Module.finrank ℝ E = 3) :
    (volume : Measure E).toSphere univ = ENNReal.ofReal (4 * Real.pi) := by
  rw [← sphere_volume_real_dim_three hdim]
  exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm

theorem sphere_volume_R3 :
    (volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere univ =
      ENNReal.ofReal (4 * Real.pi) := sphere_volume_dim_three (by simp)

theorem sphere_volume_configuration_one :
    (volume : Measure (TheoremT.Continuum.Configuration 1)).toSphere univ =
      ENNReal.ofReal (4 * Real.pi) :=
  sphere_volume_dim_three TheoremT.Continuum.configuration_one_finrank

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem integral_polar_dim_three_sphere_outer (hdim : Module.finrank ℝ E = 3)
    (f : E → F) (hf : Integrable f volume) :
    (∫ x, f x) = ∫ ω : Metric.sphere (0 : E) 1,
      (∫ r : ℝ in Ioi 0, r ^ 2 • f (r • ω.val)) ∂(volume : Measure E).toSphere := by
  letI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  simpa only [hdim, Nat.reduceSub] using integral_polar_sphere_outer volume f hf

theorem integral_polar_dim_three_radius_outer (hdim : Module.finrank ℝ E = 3)
    (f : E → F) (hf : Integrable f volume) :
    (∫ x, f x) = ∫ r : ℝ in Ioi 0, r ^ 2 •
      (∫ ω : Metric.sphere (0 : E) 1, f (r • ω.val) ∂(volume : Measure E).toSphere) := by
  letI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  simpa only [hdim, Nat.reduceSub] using integral_polar_radius_outer volume f hf

#print axioms unit_ball_volume_real_dim_three
#print axioms sphere_volume_real_dim_three
#print axioms sphere_volume_dim_three
#print axioms sphere_volume_R3
#print axioms sphere_volume_configuration_one
#print axioms integral_polar_dim_three_sphere_outer
#print axioms integral_polar_dim_three_radius_outer
end TheoremT.Polar
