import HydrogenHarmonicPolynomial_v1
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Symbolic partial differentiation agrees with actual Fréchet differentiation
of polynomial evaluation on the Euclidean space. This is the analytic bridge
needed before interpreting the algebraic harmonic decomposition physically. -/
noncomputable section
open MvPolynomial
open scoped BigOperators ContDiff
namespace TheoremT.HydrogenPolynomial

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def euclideanEvaluation (P : MvPolynomial σ ℝ) (x : EuclideanSpace ℝ σ) : ℝ :=
  eval (fun i => x i) P

theorem euclideanEvaluation_contDiff (P : MvPolynomial σ ℝ) :
    ContDiff ℝ ∞ (euclideanEvaluation P) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    change ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ σ => eval (fun i => x i) (C a))
    simpa using (contDiff_const : ContDiff ℝ ∞ (fun _ : EuclideanSpace ℝ σ => a))
  | add P Q hP hQ =>
    change ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ σ => eval (fun i => x i) (P + Q))
    simpa [euclideanEvaluation] using hP.add hQ
  | mul_X P i hP =>
    change ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ σ => eval (fun j => x j) (P * X i))
    simpa [euclideanEvaluation] using
      (hP.mul (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff)

theorem euclideanEvaluation_fderiv (P : MvPolynomial σ ℝ)
    (x v : EuclideanSpace ℝ σ) :
    fderiv ℝ (euclideanEvaluation P) x v =
      ∑ i : σ, euclideanEvaluation (pderiv i P) x * v i := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a =>
    have he : euclideanEvaluation (C a : MvPolynomial σ ℝ) = fun _ => a := by
      ext y; simp [euclideanEvaluation]
    rw [he]
    simp [euclideanEvaluation]
  | add P Q hP hQ =>
    have he : euclideanEvaluation (P + Q) =
        euclideanEvaluation P + euclideanEvaluation Q := by
      ext y; simp [euclideanEvaluation]
    rw [he, fderiv_add
      ((euclideanEvaluation_contDiff P).differentiable (by simp) x)
      ((euclideanEvaluation_contDiff Q).differentiable (by simp) x)]
    simp only [ContinuousLinearMap.add_apply, hP, hQ]
    simp [euclideanEvaluation, add_mul, Finset.sum_add_distrib]
  | mul_X P j hP =>
    have he : euclideanEvaluation (P * X j) =
        fun y => euclideanEvaluation P y * y j := by
      ext y; simp [euclideanEvaluation]
    have hc : HasFDerivAt (fun y : EuclideanSpace ℝ σ => y j)
        (EuclideanSpace.proj (𝕜 := ℝ) j) x := by
      simpa using (EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt (x := x)
    have hh := ((euclideanEvaluation_contDiff P).differentiable
      (by simp) x).hasFDerivAt.mul hc
    change HasFDerivAt (fun y => euclideanEvaluation P y * y j) _ x at hh
    rw [he, hh.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, ContinuousLinearMap.fderiv, hP]
    simp [euclideanEvaluation, pderiv_mul, pderiv_X, Pi.single_apply,
      add_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum,
      Finset.sum_mul, mul_ite, ite_mul, apply_ite, mul_assoc]

theorem euclideanEvaluation_fderiv_single (P : MvPolynomial σ ℝ)
    (x : EuclideanSpace ℝ σ) (i : σ) :
    fderiv ℝ (euclideanEvaluation P) x (EuclideanSpace.single i 1) =
      euclideanEvaluation (pderiv i P) x := by
  classical
  rw [euclideanEvaluation_fderiv]
  simp [EuclideanSpace.single_apply, Pi.single_apply]

theorem euclideanEvaluation_second_fderiv (P : MvPolynomial σ ℝ)
    (x : EuclideanSpace ℝ σ) (i j : σ) :
    fderiv ℝ (fun y => fderiv ℝ (euclideanEvaluation P) y
      (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1) =
        euclideanEvaluation (pderiv j (pderiv i P)) x := by
  simp_rw [euclideanEvaluation_fderiv_single]

theorem euclideanEvaluation_laplace (P : MvPolynomial σ ℝ)
    (x : EuclideanSpace ℝ σ) :
    (∑ i : σ, fderiv ℝ (fun y => fderiv ℝ (euclideanEvaluation P) y
      (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1)) =
        euclideanEvaluation (polynomialLaplace P) x := by
  simp [euclideanEvaluation_second_fderiv, euclideanEvaluation, polynomialLaplace]

theorem euclideanEvaluation_harmonic {P : MvPolynomial σ ℝ}
    (hP : polynomialLaplace P = 0) (x : EuclideanSpace ℝ σ) :
    (∑ i : σ, fderiv ℝ (fun y => fderiv ℝ (euclideanEvaluation P) y
      (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1)) = 0 := by
  rw [euclideanEvaluation_laplace, hP]
  simp [euclideanEvaluation]

theorem euclideanEvaluation_euler {P : MvPolynomial σ ℝ} {m : ℕ}
    (hP : P.IsHomogeneous m) (x : EuclideanSpace ℝ σ) :
    fderiv ℝ (euclideanEvaluation P) x x = (m : ℝ) * euclideanEvaluation P x := by
  rw [euclideanEvaluation_fderiv]
  have he := congrArg (eval (fun i => x i)) (polynomialEuler_of_isHomogeneous hP)
  simpa [polynomialEuler, euclideanEvaluation, mul_comm] using he

end TheoremT.HydrogenPolynomial
