import MvPolynomialCoefficientL1_v1
import MvPolynomialCoefficientL1Scaling_v1
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! A literal finite coordinate polynomial for the diagonal of a real
continuous multilinear map with complex values. Coordinate reconstruction
is explicit; the coefficient norm is bounded before any KS substitution. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum
open MvPolynomial
variable {σ E : Type*} [Fintype σ]
  [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ}

def realMultilinearCoordinatePolynomial (dirs : σ → E)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℂ) :
    MvPolynomial σ ℂ :=
  ∑ w : Fin k → σ, C (T (fun i => dirs (w i))) * ∏ i : Fin k, X (w i)

theorem realMultilinearCoordinatePolynomial_homogeneous (dirs : σ → E)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℂ) :
    (realMultilinearCoordinatePolynomial dirs T).IsHomogeneous k := by
  classical
  apply IsHomogeneous.sum
  intro w hw
  apply IsHomogeneous.C_mul
  simpa using IsHomogeneous.prod Finset.univ (fun i => X (w i)) (fun _ => 1)
    (fun i _ => isHomogeneous_X ℂ (w i))

theorem realMultilinearCoordinatePolynomial_eval (dirs : σ → E)
    (coord : E → σ → ℝ) (hreconstruct : ∀ x, ∑ j, coord x j • dirs j = x)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℂ) (x : E) :
    eval (fun j => (coord x j : ℂ)) (realMultilinearCoordinatePolynomial dirs T) =
      T (fun _ => x) := by
  classical
  have hexpand : T (fun _ => x) = ∑ w : Fin k → σ,
      T (fun i => coord x (w i) • dirs (w i)) := by
    simpa only [hreconstruct] using T.map_sum (fun (_i : Fin k) j => coord x j • dirs j)
  rw [hexpand]
  simp only [realMultilinearCoordinatePolynomial,map_sum,map_mul,eval_C,map_prod,eval_X]
  apply Finset.sum_congr rfl
  intro w hw
  rw [T.map_smul_univ]
  simp only [Complex.real_smul,Complex.ofReal_prod]
  ring

theorem polynomialCoeffL1_realMultilinearCoordinatePolynomial
    (dirs : σ → E) (T : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℂ)
    {M : ℝ} (hM : 0 ≤ M)
    (hT : ∀ w : Fin k → σ, ‖T (fun i => dirs (w i))‖ ≤ M) :
    polynomialCoeffL1 (realMultilinearCoordinatePolynomial dirs T) ≤
      (Fintype.card σ : ℝ)^k*M := by
  classical
  apply (polynomialCoeffL1_sum _ _).trans
  calc
    _ ≤ ∑ _w : Fin k → σ, M := by
      apply Finset.sum_le_sum
      intro w hw
      rw [polynomialCoeffL1_C_mul]
      have hp : polynomialCoeffL1 (∏ i : Fin k, (X (w i) : MvPolynomial σ ℂ)) ≤ 1 := by
        simpa only [polynomialCoeffL1_X,Finset.prod_const_one] using
          polynomialCoeffL1_prod (Finset.univ) (fun i : Fin k => (X (w i) : MvPolynomial σ ℂ))
      calc
        _ ≤ M*1 := mul_le_mul (hT w) hp (polynomialCoeffL1_nonneg _) hM
        _ = M := mul_one _
    _ = _ := by simp [Fintype.card_fun]

end TheoremT.Continuum
