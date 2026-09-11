import HydrogenPolynomialDensityFold_v1
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval

/-! The three-coordinate Bernstein fold is the evaluation of an actual
multivariate polynomial with finite sampled real coefficients. -/
noncomputable section
open scoped Polynomial BigOperators
namespace TheoremT.HydrogenPolynomialDensity

def polynomialInCoordinate {ι : Type*} (i : ι) (q : ℝ[X]) : MvPolynomial ι ℝ :=
  q.eval₂ MvPolynomial.C (MvPolynomial.X i)

theorem eval_polynomialInCoordinate {ι : Type*} (x : ι → ℝ) (i : ι) (q : ℝ[X]) :
    MvPolynomial.eval x (polynomialInCoordinate i q) = q.eval (x i) := by
  induction q using Polynomial.induction_on' with
  | add q r hq hr =>
    simp only [polynomialInCoordinate] at hq hr ⊢
    simp [hq, hr]
  | monomial k c => simp [polynomialInCoordinate]

def tensorBernsteinPolynomial3 (n : ℕ) (f : (Fin 3 → ℝ) → ℝ) : MvPolynomial (Fin 3) ℝ :=
  ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1), ∑ m ∈ Finset.range (n + 1),
    MvPolynomial.C (f ![(k : ℝ) / n, (l : ℝ) / n, (m : ℝ) / n]) *
      polynomialInCoordinate 0 (bernsteinPolynomial ℝ n k) *
      polynomialInCoordinate 1 (bernsteinPolynomial ℝ n l) *
      polynomialInCoordinate 2 (bernsteinPolynomial ℝ n m)

theorem tensorBernsteinPolynomial3_eval (n : ℕ) (f : (Fin 3 → ℝ) → ℝ)
    (x : Fin 3 → ℝ) :
    MvPolynomial.eval x (tensorBernsteinPolynomial3 n f) =
      coordinateFold n [0, 1, 2] f x := by
  simp only [tensorBernsteinPolynomial3, map_sum, map_mul, MvPolynomial.eval_C,
    eval_polynomialInCoordinate, coordinateFold, List.foldr_cons, List.foldr_nil]
  simp_rw [coordinateBernstein_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro m _
  have hupdate : Function.update
      (Function.update (Function.update x 0 ((k : ℝ) / n)) 1 ((l : ℝ) / n))
      2 ((m : ℝ) / n) = ![(k : ℝ) / n, (l : ℝ) / n, (m : ℝ) / n] := by
    ext i
    fin_cases i <;> simp
  rw [hupdate]
  simp only [Function.update_of_ne (by decide : (1 : Fin 3) ≠ 0),
    Function.update_of_ne (by decide : (2 : Fin 3) ≠ 0),
    Function.update_of_ne (by decide : (2 : Fin 3) ≠ 1)]
  ring

end TheoremT.HydrogenPolynomialDensity

#print axioms TheoremT.HydrogenPolynomialDensity.tensorBernsteinPolynomial3_eval
