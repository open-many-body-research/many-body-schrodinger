import HydrogenRadialLp_v1
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-! Exact physical radial integrals and norm, with the actual three-dimensional
Lebesgue measure. These identities do not use reference energy digits. -/

noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace

namespace TheoremT.Continuum

theorem configuration_one_unit_ball_volume :
    volume.real (Metric.ball (0 : Configuration 1) 1) = Real.pi * 4 / 3 := by
  rw [Measure.real, InnerProductSpace.volume_ball_of_dim_odd
    (k := 1) (by simpa using configuration_one_finrank)]
  norm_num [configuration_one_finrank, ENNReal.toReal_ofReal (by positivity :
    0 ≤ Real.pi * 4 / 3)]

theorem integral_radial_exp {a : ℝ} (ha : 0 < a) :
    (∫ x : Configuration 1, Real.exp (-a * ‖x‖)) = 8 * Real.pi / a ^ 3 := by
  rw [integral_fun_norm_addHaar (volume : Measure (Configuration 1))
    (fun r : ℝ => Real.exp (-a * r)), configuration_one_finrank,
    configuration_one_unit_ball_volume]
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 3) (by norm_num) ha
  have hi : (∫ r : ℝ in Ioi 0, r ^ 2 * Real.exp (-a * r)) = 2 / a ^ 3 := by
    convert h using 1
    · congr 1
      funext r
      norm_num [neg_mul]
    · norm_num [Real.Gamma_nat_eq_factorial, Real.rpow_natCast]
      ring
  norm_num only [Nat.reduceSub, smul_eq_mul, Nat.cast_ofNat] at *
  rw [hi]
  ring

theorem hydrogenRadialL2_norm_sq (Z : ℝ) (hZ : 0 < Z) :
    ‖hydrogenRadialL2 Z hZ‖ ^ 2 = Real.pi / Z ^ 3 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp_rw [real_inner_self_eq_norm_sq]
  calc
    (∫ x : Configuration 1, ‖hydrogenRadialL2 Z hZ x‖ ^ 2) =
        ∫ x : Configuration 1, Real.exp (-(2 * Z) * ‖x‖) := by
      apply integral_congr_ae
      filter_upwards [hydrogenRadialL2_coe_ae Z hZ] with x hx
      rw [hx]
      simp only [hydrogenRadial, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), ← Real.exp_nat_mul]
      congr 1
      ring
    _ = 8 * Real.pi / (2 * Z) ^ 3 := integral_radial_exp (by positivity)
    _ = Real.pi / Z ^ 3 := by ring

end TheoremT.Continuum
