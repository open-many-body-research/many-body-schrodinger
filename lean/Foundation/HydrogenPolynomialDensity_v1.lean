import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-! An actual first-derivative polynomial approximation theorem on a real interval.
The approximating polynomial is an anchored antiderivative of a uniformly
approximated continuous derivative. This is a prerequisite for tensor C1
approximation; it does not claim multivariate or sphere C1 density. -/

noncomputable section
open scoped Polynomial BigOperators
open Set
namespace TheoremT.HydrogenPolynomialDensity

/-- A finite coefficient formula for the polynomial primitive with zero constant term. -/
def polynomialPrimitive (q : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ q.support, Polynomial.monomial (k + 1) (q.coeff k / (k + 1 : ℕ))

theorem polynomialPrimitive_derivative (q : ℝ[X]) :
    (polynomialPrimitive q).derivative = q := by
  classical
  rw [polynomialPrimitive, Polynomial.derivative_sum]
  simp only [Polynomial.derivative_monomial, Nat.add_sub_cancel]
  have hterm (k : ℕ) : q.coeff k / (k + 1 : ℕ) * (k + 1 : ℕ) = q.coeff k := by
    apply div_mul_cancel₀
    positivity
  simp_rw [hterm]
  exact Polynomial.sum_monomial_eq q

/-- Anchoring the primitive fixes one function value exactly. -/
def anchoredPrimitive (q : ℝ[X]) (a c : ℝ) : ℝ[X] :=
  polynomialPrimitive q + Polynomial.C (c - (polynomialPrimitive q).eval a)

theorem anchoredPrimitive_eval (q : ℝ[X]) (a c : ℝ) :
    (anchoredPrimitive q a c).eval a = c := by
  simp [anchoredPrimitive]

theorem anchoredPrimitive_derivative (q : ℝ[X]) (a c : ℝ) :
    (anchoredPrimitive q a c).derivative = q := by
  simp [anchoredPrimitive, polynomialPrimitive_derivative]

/-- A derivative error bounds the anchored function error on the whole interval.
`hf` concerns the actual derivative within the interval, including its endpoints. -/
theorem anchored_derivative_error_bound {a b δ : ℝ} {f g : ℝ → ℝ}
    (hab : a ≤ b) (hδ : 0 ≤ δ)
    (hf : ∀ x ∈ Icc a b, HasDerivWithinAt f (g x) (Icc a b) x)
    (q : ℝ[X]) (hq : ∀ x ∈ Icc a b, |q.eval x - g x| ≤ δ) :
    ∀ x ∈ Icc a b,
      |(anchoredPrimitive q a (f a)).eval x - f x| ≤ δ * (b - a) := by
  let p := anchoredPrimitive q a (f a)
  have hp (x : ℝ) : HasDerivAt (fun y => p.eval y) (q.eval x) x := by
    simpa [p, anchoredPrimitive_derivative] using p.hasDerivAt x
  intro x hx
  have h := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun y hy => (hp y).hasDerivWithinAt.sub (hf y hy))
    (fun y hy => by simpa only [Real.norm_eq_abs] using hq y hy)
    (left_mem_Icc.mpr hab) hx
  have hx0 : 0 ≤ x - a := sub_nonneg.mpr hx.1
  have hx1 : x - a ≤ b - a := sub_le_sub_right hx.2 a
  simp only [Pi.sub_apply, p, anchoredPrimitive_eval, sub_self, sub_zero, Real.norm_eq_abs,
    abs_of_nonneg hx0] at h
  exact h.trans (mul_le_mul_of_nonneg_left hx1 hδ)

/-- Uniform approximation of both a function and its actual first derivative by
one polynomial, with exact interpolation at the left endpoint.
There are no polynomial-density hypotheses and no assumed derivative identity. -/
theorem exists_polynomial_C1_near {a b : ℝ} {f g : ℝ → ℝ}
    (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, HasDerivWithinAt f (g x) (Icc a b) x)
    (hg : ContinuousOn g (Icc a b)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℝ[X], p.eval a = f a ∧
      (∀ x ∈ Icc a b, |p.eval x - f x| < ε) ∧
      (∀ x ∈ Icc a b, |p.derivative.eval x - g x| < ε) := by
  let δ := ε / (1 + (b - a))
  have hlen : 0 ≤ b - a := sub_nonneg.mpr hab
  have hden : 0 < 1 + (b - a) := by linarith
  have hδ : 0 < δ := div_pos hε hden
  have hδle : δ ≤ ε := by
    dsimp [δ]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  obtain ⟨q, hq⟩ := exists_polynomial_near_of_continuousOn a b g hg δ hδ
  refine ⟨anchoredPrimitive q a (f a), anchoredPrimitive_eval _ _ _, ?_, ?_⟩
  · intro x hx
    have he := anchored_derivative_error_bound hab hδ.le hf q
      (fun y hy => (hq y hy).le) x hx
    apply he.trans_lt
    dsimp [δ]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hden).mpr
    nlinarith
  · intro x hx
    rw [anchoredPrimitive_derivative]
    exact (hq x hx).trans_le hδle

end TheoremT.HydrogenPolynomialDensity

#print axioms TheoremT.HydrogenPolynomialDensity.polynomialPrimitive_derivative
#print axioms TheoremT.HydrogenPolynomialDensity.anchored_derivative_error_bound
#print axioms TheoremT.HydrogenPolynomialDensity.exists_polynomial_C1_near
