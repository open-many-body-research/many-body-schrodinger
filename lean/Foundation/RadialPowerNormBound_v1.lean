import RadialPowerEnergy_v1

noncomputable section
open scoped RealInnerProductSpace
namespace TheoremT.Continuum

theorem radialPowerDerivative_norm_le {a b r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hr : 0 ≤ r) (z w : ℂ) (hslope : b*‖z‖^2 ≤ r*a) :
    ‖radialPowerDerivative a b z w‖ ≤ a*(1+2*r)*‖w‖ := by
  have hh := norm_add_le (a • w) ((2*b*inner ℝ z w) • z)
  change ‖radialPowerDerivative a b z w‖ ≤ _ at hh
  simp only [norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg ha,
    abs_of_nonneg hb,abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hh
  have hi := mul_le_mul_of_nonneg_right (abs_real_inner_le_norm z w)
    (show 0 ≤ 2*b*‖z‖ by positivity)
  have hs := mul_le_mul_of_nonneg_right hslope (norm_nonneg w)
  nlinarith

#print axioms radialPowerDerivative_norm_le
end TheoremT.Continuum
