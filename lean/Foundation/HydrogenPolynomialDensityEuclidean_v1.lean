import HydrogenPolynomialDensitySymmetricCube_v1
import HydrogenPolynomialCalculus_v1
import Mathlib.Analysis.Calculus.Deriv.Pi

/-! Actual Euclidean C1 polynomial density on the closed unit ball and sphere.
The source is a globally C1 function on EuclideanSpace ℝ (Fin 3), and the
conclusion controls its value and each actual Euclidean first derivative.
No extension theorem or spherical Poincare inequality is supplied as a premise. -/
noncomputable section
open scoped ContDiff
namespace TheoremT.HydrogenPolynomialDensity
open TheoremT.HydrogenPolynomial

def piToEuclidean3 : (Fin 3 → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap

theorem piToEuclidean3_apply (y : Fin 3 → ℝ) (i : Fin 3) :
    piToEuclidean3 y i = y i := rfl

theorem piToEuclidean3_ofEuclidean (x : EuclideanSpace ℝ (Fin 3)) :
    piToEuclidean3 (fun i => x i) = x := by ext i; rfl

theorem piToEuclidean3_single (i : Fin 3) :
    piToEuclidean3 (Pi.single i 1) = EuclideanSpace.single i 1 := by ext j; rfl

theorem euclidean_C1_slice_hasDerivAt {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hf : ContDiff ℝ 1 f) (i : Fin 3) (y : Fin 3 → ℝ) :
    HasDerivAt (fun t => f (piToEuclidean3 (Function.update y i t)))
      (fderiv ℝ f (piToEuclidean3 y) (EuclideanSpace.single i 1)) (y i) := by
  have hline : HasDerivAt (fun t => piToEuclidean3 (Function.update y i t))
      (EuclideanSpace.single i 1) (y i) := by
    simpa only [piToEuclidean3_single, Function.comp_def] using
      piToEuclidean3.hasFDerivAt.comp_hasDerivAt (y i) (hasDerivAt_update y i (y i))
  have hdiff := (hf.differentiable (by simp) (piToEuclidean3 y)).hasFDerivAt
  have hbase : piToEuclidean3 (Function.update y i (y i)) = piToEuclidean3 y := by simp
  rw [← hbase] at hdiff
  simpa only [Function.comp_def, hbase] using hdiff.comp_hasDerivAt (y i) hline

theorem polynomial_pi_slice_deriv_eq_euclidean (p : MvPolynomial (Fin 3) ℝ)
    (y : Fin 3 → ℝ) (i : Fin 3) :
    deriv (fun t => MvPolynomial.eval (Function.update y i t) p) (y i) =
      euclideanEvaluation (MvPolynomial.pderiv i p) (piToEuclidean3 y) := by
  have hd := euclidean_C1_slice_hasDerivAt
    ((euclideanEvaluation_contDiff p).of_le (by simp)) i y
  have he : (fun t => euclideanEvaluation p (piToEuclidean3 (Function.update y i t))) =
      (fun t => MvPolynomial.eval (Function.update y i t) p) := by
    funext t
    rfl
  rw [he, euclideanEvaluation_fderiv_single] at hd
  exact hd.deriv

/-- One polynomial uniformly approximates a globally C1 Euclidean function and
its three ambient derivative components on the closed unit ball. -/
theorem exists_polynomial_C1_near_euclidean_unitBall
    {f : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : ContDiff ℝ 1 f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : MvPolynomial (Fin 3) ℝ,
      (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 →
        |euclideanEvaluation p x - f x| < ε) ∧
      (∀ (i : Fin 3) (x : EuclideanSpace ℝ (Fin 3)), ‖x‖ ≤ 1 →
        |euclideanEvaluation (MvPolynomial.pderiv i p) x -
          fderiv ℝ f x (EuclideanSpace.single i 1)| < ε) := by
  let F : (Fin 3 → ℝ) → ℝ := fun y => f (piToEuclidean3 y)
  let G : Fin 3 → (Fin 3 → ℝ) → ℝ := fun i y =>
    fderiv ℝ f (piToEuclidean3 y) (EuclideanSpace.single i 1)
  have hF : Continuous F := hf.continuous.comp piToEuclidean3.continuous
  have hG : ∀ i, Continuous (G i) := by
    intro i
    exact ((hf.continuous_fderiv (by simp)).comp piToEuclidean3.continuous).clm_apply
      continuous_const
  obtain ⟨p, hpv, hpd⟩ := exists_mvPolynomial3_C1_near_symmetricCube hF hG
    (euclidean_C1_slice_hasDerivAt hf) hε
  have hcoord (x : EuclideanSpace ℝ (Fin 3)) (hx : ‖x‖ ≤ 1) (i : Fin 3) : |x i| ≤ 1 := by
    simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le x i).trans hx
  refine ⟨p, ?_, ?_⟩
  · intro x hx
    have hp := hpv (fun i => x i) (hcoord x hx)
    simpa only [F, euclideanEvaluation, piToEuclidean3_ofEuclidean] using hp
  · intro i x hx
    have hp := hpd i (fun j => x j) (hcoord x hx)
    rw [polynomial_pi_slice_deriv_eq_euclidean] at hp
    simpa only [G, piToEuclidean3_ofEuclidean] using hp

/-- Radius-one sphere corollary, with genuine ambient Euclidean derivatives. -/
theorem exists_polynomial_C1_near_euclidean_unitSphere
    {f : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : ContDiff ℝ 1 f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : MvPolynomial (Fin 3) ℝ,
      (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 →
        |euclideanEvaluation p x - f x| < ε) ∧
      (∀ (i : Fin 3) (x : EuclideanSpace ℝ (Fin 3)), ‖x‖ = 1 →
        |euclideanEvaluation (MvPolynomial.pderiv i p) x -
          fderiv ℝ f x (EuclideanSpace.single i 1)| < ε) := by
  obtain ⟨p, hpv, hpd⟩ := exists_polynomial_C1_near_euclidean_unitBall hf hε
  exact ⟨p, fun x hx => hpv x hx.le, fun i x hx => hpd i x hx.le⟩

end TheoremT.HydrogenPolynomialDensity

#print axioms TheoremT.HydrogenPolynomialDensity.euclidean_C1_slice_hasDerivAt
#print axioms TheoremT.HydrogenPolynomialDensity.exists_polynomial_C1_near_euclidean_unitBall
#print axioms TheoremT.HydrogenPolynomialDensity.exists_polynomial_C1_near_euclidean_unitSphere
