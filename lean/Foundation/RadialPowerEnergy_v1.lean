import RegularizedComplexNorm_v1

/-! Pointwise real-Hilbert algebra for smooth radial power tests. The estimate
is deliberately polynomial in the logarithmic slope; it does not assert the
sharper coefficient from the paper's nonsmooth truncated-power argument. -/
noncomputable section
open scoped RealInnerProductSpace
namespace TheoremT.Continuum

def radialPowerDerivative (a b : ℝ) (z w : ℂ) : ℂ :=
  a • w + (2*b*inner ℝ z w) • z

theorem radialPowerDerivative_norm_sq (a b : ℝ) (z w : ℂ) :
    ‖radialPowerDerivative a b z w‖^2 =
      a^2*‖w‖^2+(4*a*b+4*b^2*‖z‖^2)*(inner ℝ z w)^2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [radialPowerDerivative,inner_add_left,inner_add_right,
    real_inner_smul_left,real_inner_smul_right,real_inner_self_eq_norm_sq,
    real_inner_comm w z,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
  ring

theorem radialPowerDerivative_test_inner (a b : ℝ) (z w : ℂ) :
    inner ℝ w (radialPowerDerivative (a^2) (2*a*b) z w) =
      a^2*‖w‖^2+4*a*b*(inner ℝ z w)^2 := by
  simp only [radialPowerDerivative,inner_add_right,real_inner_smul_right,
    real_inner_self_eq_norm_sq,real_inner_comm w z]
  ring

theorem radial_power_energy_bound {a b r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hr : 0 ≤ r) (z w : ℂ) (hslope : b*‖z‖^2 ≤ r*a) :
    ‖radialPowerDerivative a b z w‖^2 ≤
      (1+4*r^2)*inner ℝ w (radialPowerDerivative (a^2) (2*a*b) z w) := by
  have hi : (inner ℝ z w)^2 ≤ ‖z‖^2*‖w‖^2 := by
    have h := abs_real_inner_le_norm z w
    simpa only [sq_abs,mul_pow] using pow_le_pow_left₀ (abs_nonneg _) h 2
  have hs : b^2*‖z‖^4 ≤ r^2*a^2 := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ b*‖z‖^2) hslope 2
    nlinarith
  have h1 := mul_le_mul_of_nonneg_left hi (show 0 ≤ 4*b^2*‖z‖^2 by positivity)
  have h2 := mul_le_mul_of_nonneg_right hs (sq_nonneg ‖w‖)
  have h3 : 0 ≤ r^2*a*b*(inner ℝ z w)^2 := by positivity
  rw [radialPowerDerivative_norm_sq,radialPowerDerivative_test_inner]
  nlinarith

#print axioms radialPowerDerivative_norm_sq
#print axioms radial_power_energy_bound
end TheoremT.Continuum
