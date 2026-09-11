import SmoothRadialPower_v1

/-! Pointwise identities linking the smooth nonlinear test F_{2r} to F_r.
The kinetic comparison retains the real phase contribution of complex inputs. -/
noncomputable section
open scoped RealInnerProductSpace
namespace TheoremT.Continuum

theorem smoothRadialAmplitude_double {a b r : ℝ} (ha : 0 < a) (hab : a ≤ b) (z : ℂ) :
    smoothRadialAmplitude a b (2*r) z = (smoothRadialAmplitude a b r z)^2 := by
  unfold smoothRadialAmplitude
  rw [two_mul,Real.rpow_add (smoothPowerRatio_pos ha hab (sq_nonneg _))]
  ring

theorem smoothRadialAmplitudeSlope_double {a b r : ℝ} (ha : 0 < a) (hab : a ≤ b) (z : ℂ) :
    smoothRadialAmplitudeSlope a b (2*r) z =
      2*smoothRadialAmplitude a b r z*smoothRadialAmplitudeSlope a b r z := by
  unfold smoothRadialAmplitudeSlope
  rw [smoothRadialAmplitude_double ha hab]
  ring

theorem smoothRadialPower_test_inner {a b r : ℝ} (ha : 0 < a) (hab : a ≤ b) (z : ℂ) :
    inner ℝ (smoothRadialPower a b (2*r) z) z = ‖smoothRadialPower a b r z‖^2 := by
  simp only [smoothRadialPower,real_inner_smul_left,real_inner_self_eq_norm_sq,
    norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,smoothRadialAmplitude_double ha hab]

theorem smoothRadialPower_potential_inner {a b r : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (z : ℂ) (v : ℝ) :
    inner ℝ (smoothRadialPower a b (2*r) z) (v • z) =
      inner ℝ (smoothRadialPower a b r z) (v • smoothRadialPower a b r z) := by
  rw [real_inner_smul_right,real_inner_smul_right,smoothRadialPower_test_inner ha hab,
    real_inner_self_eq_norm_sq]

theorem smoothRadialPower_energy_bound {a b r : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hr : 0 ≤ r) (z w : ℂ) :
    ‖fderiv ℝ (smoothRadialPower a b r) z w‖^2 ≤
      (1+4*r^2)*inner ℝ (fderiv ℝ (smoothRadialPower a b (2*r)) z w) w := by
  rw [smoothRadialPower_fderiv ha hab,smoothRadialPower_fderiv ha hab,
    smoothRadialAmplitude_double ha hab,smoothRadialAmplitudeSlope_double ha hab,real_inner_comm]
  exact radial_power_energy_bound (smoothRadialAmplitude_pos ha hab z).le
    (smoothRadialAmplitudeSlope_nonneg ha hab hr z) hr z w
    (smoothRadialAmplitudeSlope_bound ha hab hr z)

#print axioms smoothRadialPower_test_inner
#print axioms smoothRadialPower_potential_inner
#print axioms smoothRadialPower_energy_bound
end TheoremT.Continuum
