import CoulombLpGain_v1

/-! Polynomial dependence of the actual nonlinear Sobolev coefficient.
The finite Sobolev constant is retained exactly; no numerical value is asserted. -/
noncomputable section
open scoped NNReal
namespace TheoremT.Continuum

def coulombMoserBase (N : ℕ) (Z E : ℝ) : ℝ :=
  max 1 ((configurationSobolevConstant N : ℝ)*
    Real.sqrt (12*N*(|E|+(2*(|Z| *(N:ℝ)+(N.choose 2:ℝ)))^2)))

theorem coulombMoserBase_ge_one (N : ℕ) (Z E : ℝ) : 1 ≤ coulombMoserBase N Z E :=
  le_max_left _ _

theorem smoothPowerEnergyCoefficient_polynomial {r : ℝ} (hr : 0 ≤ r) (N : ℕ) (Z E : ℝ) :
    smoothPowerEnergyCoefficient N Z E r ≤
      4*(|E|+(2*(|Z| *(N:ℝ)+(N.choose 2:ℝ)))^2)*((2*r+1)^2)^2 := by
  have hM : 0 ≤ 1+4*r^2 := by positivity
  have hMt : 1+4*r^2 ≤ (2*r+1)^2 := by nlinarith
  have ht : 1 ≤ (2*r+1)^2 := by nlinarith
  have ht2 : (2*r+1)^2 ≤ ((2*r+1)^2)^2 := by nlinarith
  have hM2 : (1+4*r^2)^2 ≤ ((2*r+1)^2)^2 := by nlinarith
  have he := mul_le_mul_of_nonneg_right (hMt.trans ht2) (abs_nonneg E)
  have hc := mul_le_mul_of_nonneg_right hM2
    (sq_nonneg (2*(|Z| *(N:ℝ)+(N.choose 2:ℝ))))
  unfold smoothPowerEnergyCoefficient
  nlinarith

theorem smoothPowerSobolevCoefficient_polynomial {r : ℝ} (hr : 0 ≤ r) (N : ℕ) (Z E : ℝ) :
    smoothPowerSobolevCoefficient N Z E r ≤ coulombMoserBase N Z E*(2*r+1)^2 := by
  have h := mul_le_mul_of_nonneg_left (smoothPowerEnergyCoefficient_polynomial hr N Z E)
    (by positivity : 0 ≤ (3*N:ℝ))
  have he : (3*N:ℝ)*(4*(|E|+(2*(|Z| *(N:ℝ)+(N.choose 2:ℝ)))^2)*((2*r+1)^2)^2) =
      (12*N*(|E|+(2*(|Z| *(N:ℝ)+(N.choose 2:ℝ)))^2))*((2*r+1)^2)^2 := by ring
  rw [he] at h
  have hs := Real.sqrt_le_sqrt h
  rw [Real.sqrt_mul (by positivity : 0 ≤
    12*N*(|E|+(2*(|Z| *(N:ℝ)+(N.choose 2:ℝ)))^2)),
    Real.sqrt_sq (sq_nonneg (2*r+1))] at hs
  unfold smoothPowerSobolevCoefficient
  calc
    _ ≤ (configurationSobolevConstant N : ℝ)*
        (Real.sqrt (12*N*(|E|+(2*(|Z| *(N:ℝ)+(N.choose 2:ℝ)))^2))*(2*r+1)^2) :=
      mul_le_mul_of_nonneg_left hs (NNReal.coe_nonneg _)
    _ ≤ coulombMoserBase N Z E*(2*r+1)^2 := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)

#print axioms smoothPowerSobolevCoefficient_polynomial
end TheoremT.Continuum
