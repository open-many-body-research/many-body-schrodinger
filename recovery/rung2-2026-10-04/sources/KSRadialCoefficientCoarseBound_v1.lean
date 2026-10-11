import KSRadialCoefficientL1_v1

/-! A convenient base-two consequence of the sharper radial coefficient bound. -/
noncomputable section
set_option autoImplicit false
namespace TheoremT.Continuum

theorem three_pow_half_le_two_pow (m : ℕ) :
    (3 : ℝ)^(m/2) ≤ (2 : ℝ)^m := by
  calc
    (3 : ℝ)^(m/2) ≤ (4 : ℝ)^(m/2) :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) _
    _ = (2 : ℝ)^(2*(m/2)) := by
      rw [show (4 : ℝ) = 2^2 by norm_num, ← pow_mul]
    _ ≤ (2 : ℝ)^m := pow_le_pow_right₀ (by norm_num) (by omega)

theorem polynomialCoeffL1_ksRadial_combined_coarse_bound
    (P : MvPolynomial (Fin 4) ℂ) {m : ℕ} (hm : P.totalDegree ≤ m) :
    polynomialCoeffL1 (ksRadialEven P) + polynomialCoeffL1 (ksRadialOdd P) ≤
      polynomialCoeffL1 P * (2 : ℝ)^m :=
  (polynomialCoeffL1_ksRadial_combined_degree_bound P hm).trans
    (mul_le_mul_of_nonneg_left (three_pow_half_le_two_pow m) (polynomialCoeffL1_nonneg P))

end TheoremT.Continuum
