import ContinuumFoundation_v1
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-!
The actual three-dimensional hydrogen radial exponential and its Coulomb
quotient belong to L2 for every positive real charge.  These are integrability
statements only: no differentiability at the origin is asserted here.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal

namespace TheoremT.Continuum

def hydrogenRadial (Z : ℝ) (x : Configuration 1) : ℂ :=
  (Real.exp (-Z * ‖x‖) : ℂ)

theorem hydrogenRadial_continuous (Z : ℝ) : Continuous (hydrogenRadial Z) := by
  unfold hydrogenRadial
  fun_prop

theorem configuration_one_finrank : Module.finrank ℝ (Configuration 1) = 3 := by
  simp [Configuration, Coordinate]

theorem integrable_radial_exp (a : ℝ) (ha : 0 < a) :
    Integrable (fun x : Configuration 1 => Real.exp (-a * ‖x‖)) := by
  apply (integrable_fun_norm_addHaar (volume : Measure (Configuration 1))
    (f := fun r : ℝ => Real.exp (-a * r))).2
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (s := 2) (p := 1) (b := a) (by norm_num) (by norm_num) ha
  simpa [configuration_one_finrank, Real.rpow_two, smul_eq_mul] using h

theorem integrable_radial_exp_div_sq_norm (a : ℝ) (ha : 0 < a) :
    Integrable (fun x : Configuration 1 => Real.exp (-a * ‖x‖) / ‖x‖ ^ 2) := by
  apply (integrable_fun_norm_addHaar (volume : Measure (Configuration 1))
    (f := fun r : ℝ => Real.exp (-a * r) / r ^ 2)).2
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (s := 0) (p := 1) (b := a) (by norm_num) (by norm_num) ha
  have he : IntegrableOn (fun r : ℝ => Real.exp (-a * r)) (Ioi 0) := by
    simpa using h
  apply he.congr_fun _ measurableSet_Ioi
  intro r hr
  simp only [configuration_one_finrank, Nat.reduceSub, smul_eq_mul]
  field_simp [ne_of_gt (mem_Ioi.mp hr)]

theorem hydrogenRadial_memLp {Z : ℝ} (hZ : 0 < Z) :
    MemLp (hydrogenRadial Z) 2 (volume : Measure (Configuration 1)) := by
  apply (memLp_two_iff_integrable_sq_norm (hydrogenRadial_continuous Z).aestronglyMeasurable).2
  have he : (fun x : Configuration 1 => ‖hydrogenRadial Z x‖ ^ 2) =
      (fun x => Real.exp (-(2 * Z) * ‖x‖)) := by
    funext x
    simp only [hydrogenRadial, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), ← Real.exp_nat_mul]
    congr 1
    ring
  rw [he]
  exact integrable_radial_exp (2 * Z) (by positivity)

theorem hydrogenRadial_div_norm_memLp {Z : ℝ} (hZ : 0 < Z) :
    MemLp (fun x : Configuration 1 => hydrogenRadial Z x / (‖x‖ : ℂ)) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm
    (((hydrogenRadial_continuous Z).measurable.div (by fun_prop)).aestronglyMeasurable)).2
  have he : (fun x : Configuration 1 => ‖hydrogenRadial Z x / (‖x‖ : ℂ)‖ ^ 2) =
      (fun x => Real.exp (-(2 * Z) * ‖x‖) / ‖x‖ ^ 2) := by
    funext x
    simp only [hydrogenRadial, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), abs_norm, div_pow, ← Real.exp_nat_mul]
    congr 2
    ring
  change Integrable (fun x : Configuration 1 => ‖hydrogenRadial Z x / (‖x‖ : ℂ)‖ ^ 2)
  rw [he]
  exact integrable_radial_exp_div_sq_norm (2 * Z) (by positivity)

def hydrogenRadialL2 (Z : ℝ) (hZ : 0 < Z) : SpatialL2 1 :=
  (hydrogenRadial_memLp hZ).toLp (hydrogenRadial Z)

theorem hydrogenRadialL2_coe_ae (Z : ℝ) (hZ : 0 < Z) :
    hydrogenRadialL2 Z hZ =ᵐ[volume] hydrogenRadial Z :=
  (hydrogenRadial_memLp hZ).coeFn_toLp

theorem hydrogenRadialL2_ne_zero (Z : ℝ) (hZ : 0 < Z) :
    hydrogenRadialL2 Z hZ ≠ 0 := by
  intro hz
  have he : hydrogenRadial Z =ᵐ[volume] (fun _ : Configuration 1 => (0 : ℂ)) := by
    filter_upwards [(hydrogenRadialL2_coe_ae Z hZ).symm, Lp.coeFn_zero (E := ℂ)
      (p := (2 : ℝ≥0∞)) (μ := (volume : Measure (Configuration 1)))] with x hx hx0
    rw [hx, hz]
    exact hx0
  have hfun := ((hydrogenRadial_continuous Z).ae_eq_iff_eq volume continuous_const).mp he
  have hzero := congrFun hfun 0
  simpa [hydrogenRadial] using hzero

end TheoremT.Continuum
