import HydrogenRadialPowerCalculus_v1

/-! The homogeneous degree-zero extension of an actual harmonic polynomial has
zero radial derivative and Euclidean Laplacian -m(m+1)/r² times itself in three
dimensions. The assertions hold away from the origin; no spherical spectrum or
angular integration inequality is assumed. -/
noncomputable section
open MvPolynomial
open scoped BigOperators ContDiff Topology
namespace TheoremT.HydrogenPolynomial

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def radialPolynomialProduct (a : ℝ) (P : MvPolynomial σ ℝ)
    (x : EuclideanSpace ℝ σ) : ℝ := radialSquaredPower a x * euclideanEvaluation P x

theorem radialPolynomialProduct_fderiv_single (a : ℝ) (P : MvPolynomial σ ℝ)
    {x : EuclideanSpace ℝ σ} (hx : x ≠ 0) (i : σ) :
    fderiv ℝ (radialPolynomialProduct a P) x (EuclideanSpace.single i 1) =
      radialSquaredPower a x * euclideanEvaluation (pderiv i P) x +
        (2 * a * x i * radialSquaredPower (a - 1) x) * euclideanEvaluation P x := by
  have hh := (radialSquaredPower_hasFDerivAt a hx).mul
    ((euclideanEvaluation_contDiff P).differentiable (by simp) x).hasFDerivAt
  change HasFDerivAt (radialPolynomialProduct a P) _ x at hh
  rw [hh.fderiv]
  simp [euclideanEvaluation_fderiv_single, radialSquaredPower,
    EuclideanSpace.inner_single_right]
  ring

theorem radialPolynomialProduct_second_fderiv_single (a : ℝ)
    (P : MvPolynomial σ ℝ) {x : EuclideanSpace ℝ σ} (hx : x ≠ 0) (i : σ) :
    fderiv ℝ (fun y => fderiv ℝ (radialPolynomialProduct a P) y
      (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1) =
      radialSquaredPower a x * euclideanEvaluation (pderiv i (pderiv i P)) x +
      4 * a * x i * radialSquaredPower (a - 1) x * euclideanEvaluation (pderiv i P) x +
      (2 * a * radialSquaredPower (a - 1) x +
        4 * a * (a - 1) * (x i) ^ 2 * radialSquaredPower (a - 2) x) *
          euclideanEvaluation P x := by
  have he : (fun y => fderiv ℝ (radialPolynomialProduct a P) y
      (EuclideanSpace.single i 1)) =ᶠ[𝓝 x]
      (fun y => radialSquaredPower a y * euclideanEvaluation (pderiv i P) y +
        (2 * a * y i * radialSquaredPower (a - 1) y) * euclideanEvaluation P y) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hx] with y hy
    exact radialPolynomialProduct_fderiv_single a P hy i
  rw [he.fderiv_eq]
  have hc : HasFDerivAt (fun y : EuclideanSpace ℝ σ => y i)
      (EuclideanSpace.proj (𝕜 := ℝ) i) x := by
    simpa using (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt (x := x)
  have hP := ((euclideanEvaluation_contDiff P).differentiable (by simp) x).hasFDerivAt
  have hPi := ((euclideanEvaluation_contDiff (pderiv i P)).differentiable
    (by simp) x).hasFDerivAt
  have hh := ((radialSquaredPower_hasFDerivAt a hx).mul hPi).add
    (((hc.const_mul (2 * a)).mul (radialSquaredPower_hasFDerivAt (a - 1) hx)).mul hP)
  change HasFDerivAt (fun y => radialSquaredPower a y * euclideanEvaluation (pderiv i P) y +
    (2 * a * y i * radialSquaredPower (a - 1) y) * euclideanEvaluation P y) _ x at hh
  rw [hh.fderiv]
  simp [euclideanEvaluation_fderiv_single, radialSquaredPower,
    EuclideanSpace.inner_single_right, show a - 1 - 1 = a - 2 by ring]
  ring

theorem radialPolynomialProduct_laplace_harmonic (a : ℝ)
    {P : MvPolynomial σ ℝ} {m : ℕ} (hP : P.IsHomogeneous m)
    (hL : polynomialLaplace P = 0) {x : EuclideanSpace ℝ σ} (hx : x ≠ 0) :
    (∑ i : σ, fderiv ℝ (fun y => fderiv ℝ (radialPolynomialProduct a P) y
      (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1)) =
      2 * a * ((Fintype.card σ : ℝ) + 2 * m + 2 * a - 2) *
        radialSquaredPower (a - 1) x * euclideanEvaluation P x := by
  have hE := euclideanEvaluation_euler hP x
  rw [euclideanEvaluation_fderiv] at hE
  have hD : (∑ i : σ, euclideanEvaluation (pderiv i (pderiv i P)) x) = 0 := by
    simpa [euclideanEvaluation, polynomialLaplace] using
      congrArg (eval (fun i => x i)) hL
  have hS := EuclideanSpace.real_norm_sq_eq x
  have hn : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
  have hr : radialSquaredPower (a - 2) x * ‖x‖ ^ 2 = radialSquaredPower (a - 1) x := by
    dsimp [radialSquaredPower]
    rw [← Real.rpow_add_one hn]
    congr 1
    ring
  simp_rw [radialPolynomialProduct_second_fderiv_single a P hx]
  calc
    _ = ∑ i : σ, (radialSquaredPower a x * euclideanEvaluation (pderiv i (pderiv i P)) x +
        (4 * a * radialSquaredPower (a - 1) x) * (euclideanEvaluation (pderiv i P) x * x i) +
        (2 * a * radialSquaredPower (a - 1) x * euclideanEvaluation P x) +
        (4 * a * (a - 1) * radialSquaredPower (a - 2) x * euclideanEvaluation P x) * (x i)^2) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = radialSquaredPower a x * (∑ i, euclideanEvaluation (pderiv i (pderiv i P)) x) +
      4 * a * radialSquaredPower (a - 1) x * (∑ i, euclideanEvaluation (pderiv i P) x * x i) +
      ((Fintype.card σ : ℝ) * (2 * a * radialSquaredPower (a - 1) x) +
        4 * a * (a - 1) * (radialSquaredPower (a - 2) x * ∑ i, (x i)^2)) *
          euclideanEvaluation P x := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
    _ = _ := by rw [hD, hE, ← hS, hr]; ring

theorem radialPolynomialProduct_fderiv_radial (a : ℝ)
    {P : MvPolynomial σ ℝ} {m : ℕ} (hP : P.IsHomogeneous m)
    {x : EuclideanSpace ℝ σ} (hx : x ≠ 0) :
    fderiv ℝ (radialPolynomialProduct a P) x x =
      (2 * a + m) * radialPolynomialProduct a P x := by
  have he : radialPolynomialProduct a P =
      fun y => radialSquaredPower a y * euclideanEvaluation P y := rfl
  rw [he, fderiv_fun_mul (radialSquaredPower_hasFDerivAt a hx).differentiableAt
    ((euclideanEvaluation_contDiff P).differentiable (by simp) x)]
  simp [euclideanEvaluation_euler hP, radialSquaredPower_fderiv_radial a hx,
    radialPolynomialProduct]
  ring

def harmonicAngularExtension (m : ℕ) (P : MvPolynomial (Fin 3) ℝ) :
    EuclideanSpace ℝ (Fin 3) → ℝ := radialPolynomialProduct (-(m : ℝ) / 2) P

theorem harmonicAngularExtension_radial_zero {P : MvPolynomial (Fin 3) ℝ} {m : ℕ}
    (hP : P.IsHomogeneous m) {x : EuclideanSpace ℝ (Fin 3)} (hx : x ≠ 0) :
    fderiv ℝ (harmonicAngularExtension m P) x x = 0 := by
  rw [harmonicAngularExtension, radialPolynomialProduct_fderiv_radial _ hP hx]
  ring

theorem harmonicAngularExtension_laplace {P : MvPolynomial (Fin 3) ℝ} {m : ℕ}
    (hP : P.IsHomogeneous m) (hL : polynomialLaplace P = 0)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ≠ 0) :
    (∑ i : Fin 3, fderiv ℝ (fun y => fderiv ℝ (harmonicAngularExtension m P) y
      (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1)) =
      -((m : ℝ) * (m + 1)) / ‖x‖ ^ 2 * harmonicAngularExtension m P x := by
  rw [harmonicAngularExtension, radialPolynomialProduct_laplace_harmonic _ hP hL hx]
  have hn : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
  simp only [Fintype.card_fin, Nat.cast_ofNat]
  dsimp [radialSquaredPower, harmonicAngularExtension, radialPolynomialProduct]
  rw [Real.rpow_sub_one hn]
  ring

end TheoremT.HydrogenPolynomial
