import HydrogenAngularExtension_v1
import HydrogenSpherePolynomialSpan_v1

/-! Actual polynomial scaling and geometric interpretation of the angular
extension on the Euclidean unit sphere. -/
noncomputable section
open MvPolynomial
open scoped BigOperators ContDiff
namespace TheoremT.HydrogenPolynomial

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem homogeneous_eval_scale {P : MvPolynomial σ ℝ} {m : ℕ}
    (hP : P.IsHomogeneous m) (c : ℝ) (x : σ → ℝ) :
    eval (fun i => c * x i) P = c ^ m * eval x P := by
  rw [eval_eq, eval_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [show m = ∑ i ∈ d.support, d i from hP.degree_eq_sum_deg_support hd]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring

theorem euclideanEvaluation_scale {P : MvPolynomial σ ℝ} {m : ℕ}
    (hP : P.IsHomogeneous m) (c : ℝ) (x : EuclideanSpace ℝ σ) :
    euclideanEvaluation P (c • x) = c ^ m * euclideanEvaluation P x := by
  simpa [euclideanEvaluation, smul_eq_mul] using homogeneous_eval_scale hP c (fun i => x i)

theorem radialSquaredPower_neg_half_nat (m : ℕ) (x : EuclideanSpace ℝ σ) :
    radialSquaredPower (-(m : ℝ) / 2) x = (‖x‖ ^ m)⁻¹ := by
  dsimp [radialSquaredPower]
  rw [← Real.rpow_natCast_mul (norm_nonneg x)]
  norm_num only [Nat.cast_ofNat]
  rw [show (2 : ℝ) * (-(m : ℝ) / 2) = -(m : ℝ) by ring,
    Real.rpow_neg (norm_nonneg x), Real.rpow_natCast]

theorem harmonicAngularExtension_scale {P : MvPolynomial (Fin 3) ℝ} {m : ℕ}
    (hP : P.IsHomogeneous m) {c : ℝ} (hc : 0 < c)
    (x : EuclideanSpace ℝ (Fin 3)) :
    harmonicAngularExtension m P (c • x) = harmonicAngularExtension m P x := by
  simp only [harmonicAngularExtension, radialPolynomialProduct,
    radialSquaredPower_neg_half_nat, euclideanEvaluation_scale hP, norm_smul,
    Real.norm_eq_abs, abs_of_pos hc, mul_pow, mul_inv_rev]
  have hpow : c ^ m ≠ 0 := pow_ne_zero _ hc.ne'
  field_simp

theorem harmonicAngularExtension_unitSphere (m : ℕ) (P : MvPolynomial (Fin 3) ℝ)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : ‖x‖ = 1) :
    harmonicAngularExtension m P x = euclideanEvaluation P x := by
  simp [harmonicAngularExtension, radialPolynomialProduct, radialSquaredPower, hx]

def geometricSphereToAlgebraic (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    UnitSphere3 :=
  ⟨(fun i => x.val i), by
    have hx : ‖x.val‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using x.property
    rw [← EuclideanSpace.real_norm_sq_eq, hx]
    norm_num⟩

theorem harmonicAngularExtension_algebraicSphere (m : ℕ) (P : Polynomial3)
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    harmonicAngularExtension m P x.val =
      spherePolynomialEvaluation P (geometricSphereToAlgebraic x) := by
  rw [harmonicAngularExtension_unitSphere m P
    (by simpa [Metric.mem_sphere, dist_zero_right] using x.property)]
  rfl

end TheoremT.HydrogenPolynomial
