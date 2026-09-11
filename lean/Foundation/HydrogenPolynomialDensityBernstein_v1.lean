import HydrogenPolynomialDensity_v1
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Actual finite Bernstein polynomials and their first derivatives.
The derivative is the degree times the Bernstein average of forward differences.
This algebraic identity is the bridge required by tensor C1 approximation. -/
noncomputable section
open scoped Polynomial BigOperators unitInterval
open Set
namespace TheoremT.HydrogenPolynomialDensity

def bernsteinCombination (n : ℕ) (c : ℕ → ℝ) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1), Polynomial.C (c k) * bernsteinPolynomial ℝ n k

theorem bernsteinCombination_derivative (n : ℕ) (c : ℕ → ℝ) :
    (bernsteinCombination (n + 1) c).derivative =
      Polynomial.C (n + 1 : ℝ) * bernsteinCombination n (fun k => c (k + 1) - c k) := by
  classical
  rw [bernsteinCombination, Polynomial.derivative_sum]
  simp only [Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add]
  rw [Finset.sum_range_succ']
  simp only [bernsteinPolynomial.derivative_succ_aux, bernsteinPolynomial.derivative_zero,
    Nat.add_sub_cancel]
  have hz : bernsteinPolynomial ℝ n (n + 1) = 0 :=
    bernsteinPolynomial.eq_zero_of_lt ℝ (Nat.lt_succ_self n)
  have hs :
      (∑ k ∈ Finset.range (n + 1), Polynomial.C (c (k + 1)) *
        bernsteinPolynomial ℝ n (k + 1)) + Polynomial.C (c 0) * bernsteinPolynomial ℝ n 0 =
      ∑ k ∈ Finset.range (n + 1), Polynomial.C (c k) * bernsteinPolynomial ℝ n k := by
    rw [← Finset.sum_range_succ' (fun k => Polynomial.C (c k) *
      bernsteinPolynomial ℝ n k) (n + 1)]
    rw [Finset.sum_range_succ]
    simp [hz]
  simp only [bernsteinCombination, map_sub, mul_sub, sub_mul, Finset.sum_sub_distrib,
    Finset.mul_sum]
  simp_rw [← mul_assoc, mul_comm (Polynomial.C _) ((n : ℝ[X]) + 1), mul_assoc]
  simp only [← Finset.mul_sum]
  have hcast : Polynomial.C (n + 1 : ℝ) = (n : ℝ[X]) + 1 := by simp
  rw [hcast]
  push_cast
  linear_combination -((n : ℝ[X]) + 1) * hs

def gridBernsteinPolynomial (n : ℕ) (f : ℝ → ℝ) : ℝ[X] :=
  bernsteinCombination n (fun k => f ((k : ℝ) / n))

def forwardGridDifference (n k : ℕ) (f : ℝ → ℝ) : ℝ :=
  (n + 1 : ℝ) * (f ((k + 1 : ℕ) / (n + 1 : ℝ)) - f ((k : ℝ) / (n + 1 : ℝ)))

theorem gridBernsteinPolynomial_derivative (n : ℕ) (f : ℝ → ℝ) :
    (gridBernsteinPolynomial (n + 1) f).derivative =
      bernsteinCombination n (fun k => forwardGridDifference n k f) := by
  rw [gridBernsteinPolynomial, bernsteinCombination_derivative]
  simp only [bernsteinCombination, forwardGridDifference, Polynomial.C_mul,
    Polynomial.C_sub, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Nat.cast_add, Nat.cast_one]
  ring

theorem gridBernsteinPolynomial_hasDerivAt (n : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    HasDerivAt (fun y => (gridBernsteinPolynomial (n + 1) f).eval y)
      ((bernsteinCombination n (fun k => forwardGridDifference n k f)).eval x) x := by
  simpa only [gridBernsteinPolynomial_derivative] using
    (gridBernsteinPolynomial (n + 1) f).hasDerivAt x

end TheoremT.HydrogenPolynomialDensity

#print axioms TheoremT.HydrogenPolynomialDensity.bernsteinCombination_derivative
#print axioms TheoremT.HydrogenPolynomialDensity.gridBernsteinPolynomial_derivative
#print axioms TheoremT.HydrogenPolynomialDensity.gridBernsteinPolynomial_hasDerivAt
