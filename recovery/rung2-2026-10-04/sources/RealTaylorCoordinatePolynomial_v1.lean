import RealMultilinearCoordinatePolynomial_v1
import FactorialFrechetSeries_v1

/-! Literal coordinate polynomials of the actual Frechet derivative series.
The coefficient budget is deduced from coordinate evaluations of the actual
derivatives, and the series sum is linked to the given function. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators ENNReal
namespace TheoremT.Continuum
open MvPolynomial
variable {σ E : Type*} [Fintype σ]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def realTaylorCoordinatePolynomial (dirs : σ → E) (f : E → ℂ) (x : E) (k : ℕ) :
    MvPolynomial σ ℂ :=
  realMultilinearCoordinatePolynomial dirs (factorialFrechetSeries f x k)

theorem realTaylorCoordinatePolynomial_homogeneous
    (dirs : σ → E) (f : E → ℂ) (x : E) (k : ℕ) :
    (realTaylorCoordinatePolynomial dirs f x k).IsHomogeneous k :=
  realMultilinearCoordinatePolynomial_homogeneous dirs (factorialFrechetSeries f x k)

theorem realTaylorCoordinatePolynomial_eval (dirs : σ → E)
    (coord : E → σ → ℝ) (hreconstruct : ∀ y, ∑ j, coord y j • dirs j = y)
    (f : E → ℂ) (x y : E) (k : ℕ) :
    eval (fun j => (coord y j : ℂ)) (realTaylorCoordinatePolynomial dirs f x k) =
      factorialFrechetSeries f x k (fun _ => y) :=
  realMultilinearCoordinatePolynomial_eval dirs coord hreconstruct _ y

theorem polynomialCoeffL1_realTaylorCoordinatePolynomial
    (dirs : σ → E) (f : E → ℂ) (x : E) (k : ℕ)
    {M A : ℝ} (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hbound : ∀ w : Fin k → σ,
      ‖iteratedFDeriv ℝ k f x (fun i => dirs (w i))‖ ≤ M*A^k*(k.factorial : ℝ)) :
    polynomialCoeffL1 (realTaylorCoordinatePolynomial dirs f x k) ≤
      M*((Fintype.card σ : ℝ)*A)^k := by
  have hT (w : Fin k → σ) :
      ‖factorialFrechetSeries f x k (fun i => dirs (w i))‖ ≤ M*A^k := by
    rw [factorialFrechetSeries_apply,norm_smul,
      Real.norm_of_nonneg (by positivity : 0 ≤ (k.factorial : ℝ)⁻¹)]
    calc
      _ ≤ (k.factorial : ℝ)⁻¹*(M*A^k*(k.factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left (hbound w) (by positivity)
      _ = M*A^k := by field_simp
  calc
    _ ≤ (Fintype.card σ : ℝ)^k*(M*A^k) :=
      polynomialCoeffL1_realMultilinearCoordinatePolynomial dirs _ (mul_nonneg hM (pow_nonneg hA _)) hT
    _ = _ := by rw [mul_pow]; ring

theorem realTaylorCoordinatePolynomial_hasSum (dirs : σ → E)
    (coord : E → σ → ℝ) (hreconstruct : ∀ y, ∑ j, coord y j • dirs j = y)
    (f : E → ℂ) (x : E) {r : ℝ≥0∞}
    (hseries : HasFPowerSeriesOnBall f (factorialFrechetSeries f x) x r)
    {y : E} (hy : y ∈ Metric.eball 0 r) :
    HasSum (fun k => eval (fun j => (coord y j : ℂ))
      (realTaylorCoordinatePolynomial dirs f x k)) (f (x+y)) := by
  simpa only [realTaylorCoordinatePolynomial_eval dirs coord hreconstruct] using hseries.hasSum hy

end TheoremT.Continuum
