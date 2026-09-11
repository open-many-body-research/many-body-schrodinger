import HydrogenSphereTangential_v1
import HydrogenPolynomialDensityEuclidean_v1

/-! Uniform ambient derivative approximation implies uniform approximation of
the actual tangential derivative on the Euclidean unit sphere. -/
noncomputable section
open scoped BigOperators ContDiff
namespace TheoremT.HydrogenSphereC1Limit
open TheoremT.HydrogenPolynomial

theorem euclidean_single_expansion (x : AngularR3) :
    ∑ i : Fin 3, x i • EuclideanSpace.single i 1 = x := by
  ext j
  simp [Pi.single_apply]

theorem fderiv_radial_eq_sum (f : AngularR3 → ℝ) (x : AngularR3) :
    fderiv ℝ f x x = ∑ i : Fin 3, x i * euclideanPartial i f x := by
  calc
    fderiv ℝ f x x = fderiv ℝ f x (∑ i : Fin 3, x i • EuclideanSpace.single i 1) :=
      congrArg (fderiv ℝ f x) (euclidean_single_expansion x).symm
    _ = _ := by simp only [map_sum, map_smul, smul_eq_mul, euclideanPartial]

theorem continuous_tangentialPartial {f : AngularR3 → ℝ}
    (hf : ContDiff ℝ 1 f) (i : Fin 3) : Continuous (tangentialPartial i f) := by
  exact ((hf.continuous_fderiv (by simp)).clm_apply continuous_const).sub
    ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i).mul
      ((hf.continuous_fderiv (by simp)).clm_apply continuous_id))

theorem tangentialPartial_error_le {f g : AngularR3 → ℝ} {δ : ℝ}
    (hδ : 0 ≤ δ) {x : AngularR3} (hx : ‖x‖ = 1)
    (herr : ∀ j : Fin 3, |euclideanPartial j f x - euclideanPartial j g x| ≤ δ)
    (i : Fin 3) : |tangentialPartial i f x - tangentialPartial i g x| ≤ 4 * δ := by
  have hcoord (j : Fin 3) : |x j| ≤ 1 := by
    simpa only [Real.norm_eq_abs, hx] using PiLp.norm_apply_le x j
  have hrad : |fderiv ℝ f x x - fderiv ℝ g x x| ≤ 3 * δ := by
    rw [fderiv_radial_eq_sum, fderiv_radial_eq_sum, ← Finset.sum_sub_distrib]
    calc
      |∑ j : Fin 3, (x j * euclideanPartial j f x - x j * euclideanPartial j g x)| ≤
          ∑ j : Fin 3, |x j * euclideanPartial j f x - x j * euclideanPartial j g x| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin 3, δ := by
        apply Finset.sum_le_sum
        intro j _
        rw [← mul_sub, abs_mul]
        exact (mul_le_mul_of_nonneg_left (herr j) (abs_nonneg _)).trans
          (by simpa using mul_le_mul_of_nonneg_right (hcoord j) hδ)
      _ = 3 * δ := by simp
  have he : tangentialPartial i f x - tangentialPartial i g x =
      (euclideanPartial i f x - euclideanPartial i g x) -
        x i * (fderiv ℝ f x x - fderiv ℝ g x x) := by
    unfold tangentialPartial
    ring
  rw [he]
  calc
    _ ≤ |euclideanPartial i f x - euclideanPartial i g x| +
        |x i * (fderiv ℝ f x x - fderiv ℝ g x x)| := abs_sub _ _
    _ ≤ δ + 3 * δ := by
      apply add_le_add (herr i)
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left hrad (abs_nonneg _)).trans
        (by simpa using mul_le_mul_of_nonneg_right (hcoord i) (by positivity : 0 ≤ 3 * δ))
    _ = 4 * δ := by ring

end TheoremT.HydrogenSphereC1Limit

#print axioms TheoremT.HydrogenSphereC1Limit.tangentialPartial_error_le
