import HydrogenPolynomialCalculus_v1
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! Actual first and second coordinate derivatives of real powers of squared
Euclidean radius away from the origin. Exponents can be negative. -/
noncomputable section
open scoped BigOperators ContDiff RealInnerProductSpace Topology
namespace TheoremT.HydrogenPolynomial

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def radialSquaredPower (a : ℝ) (x : EuclideanSpace ℝ σ) : ℝ := (‖x‖ ^ 2) ^ a

theorem radialSquaredPower_hasFDerivAt (a : ℝ) {x : EuclideanSpace ℝ σ}
    (hx : x ≠ 0) : HasFDerivAt (radialSquaredPower a)
      ((a * (‖x‖ ^ 2) ^ (a - 1)) • (2 • innerSL ℝ x)) x := by
  exact (hasStrictFDerivAt_norm_sq x).hasFDerivAt.rpow_const
    (Or.inl (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)))

theorem radialSquaredPower_fderiv_single (a : ℝ) {x : EuclideanSpace ℝ σ}
    (hx : x ≠ 0) (i : σ) :
    fderiv ℝ (radialSquaredPower a) x (EuclideanSpace.single i 1) =
      2 * a * x i * (‖x‖ ^ 2) ^ (a - 1) := by
  rw [(radialSquaredPower_hasFDerivAt a hx).fderiv]
  simp [EuclideanSpace.inner_single_right]
  ring

theorem radialSquaredPower_fderiv_radial (a : ℝ) {x : EuclideanSpace ℝ σ}
    (hx : x ≠ 0) :
    fderiv ℝ (radialSquaredPower a) x x = 2 * a * radialSquaredPower a x := by
  rw [(radialSquaredPower_hasFDerivAt a hx).fderiv]
  have hn : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, innerSL_apply_apply,
    real_inner_self_eq_norm_sq]
  rw [Real.rpow_sub_one hn]
  dsimp [radialSquaredPower]
  field_simp
  <;> ring

theorem radialSquaredPower_second_fderiv_single (a : ℝ) {x : EuclideanSpace ℝ σ}
    (hx : x ≠ 0) (i : σ) :
    fderiv ℝ (fun y => fderiv ℝ (radialSquaredPower a) y
      (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1) =
        2 * a * (‖x‖ ^ 2) ^ (a - 1) +
          4 * a * (a - 1) * (x i) ^ 2 * (‖x‖ ^ 2) ^ (a - 2) := by
  have he : (fun y => fderiv ℝ (radialSquaredPower a) y
      (EuclideanSpace.single i 1)) =ᶠ[𝓝 x]
        (fun y => 2 * a * y i * radialSquaredPower (a - 1) y) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hx] with y hy
    exact radialSquaredPower_fderiv_single a hy i
  rw [he.fderiv_eq]
  have hc : HasFDerivAt (fun y : EuclideanSpace ℝ σ => y i)
      (EuclideanSpace.proj (𝕜 := ℝ) i) x := by
    simpa using (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt (x := x)
  have hh := (hc.const_mul (2 * a)).mul (radialSquaredPower_hasFDerivAt (a - 1) hx)
  change HasFDerivAt (fun y => 2 * a * y i * radialSquaredPower (a - 1) y) _ x at hh
  rw [hh.fderiv]
  simp [radialSquaredPower, EuclideanSpace.inner_single_right,
    show a - 1 - 1 = a - 2 by ring]
  ring

theorem radialSquaredPower_laplace (a : ℝ) {x : EuclideanSpace ℝ σ}
    (hx : x ≠ 0) :
    (∑ i : σ, fderiv ℝ (fun y => fderiv ℝ (radialSquaredPower a) y
      (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1)) =
      2 * a * ((Fintype.card σ : ℝ) + 2 * a - 2) * (‖x‖ ^ 2) ^ (a - 1) := by
  simp_rw [radialSquaredPower_second_fderiv_single a hx]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Finset.sum_mul, ← Finset.mul_sum, ← EuclideanSpace.real_norm_sq_eq]
  have hn : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
  have hr : (‖x‖ ^ 2) ^ (a - 2) * ‖x‖ ^ 2 = (‖x‖ ^ 2) ^ (a - 1) := by
    rw [← Real.rpow_add_one hn]
    congr 1
    ring
  calc
    _ = (Fintype.card σ : ℝ) * (2 * a * (‖x‖ ^ 2) ^ (a - 1)) +
      4 * a * (a - 1) * ((‖x‖ ^ 2) ^ (a - 2) * ‖x‖ ^ 2) := by ring
    _ = _ := by rw [hr]; ring

end TheoremT.HydrogenPolynomial
