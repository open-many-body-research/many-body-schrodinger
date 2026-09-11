import HydrogenRadialCalculus_v2

/-! Exact regularized hydrogen Laplacian in the actual three-dimensional
one-electron configuration space, with the physical coordinate basis. -/
noncomputable section
set_option maxHeartbeats 1600000
open scoped BigOperators RealInnerProductSpace ContDiff
namespace TheoremT.Continuum

theorem hydrogenSmoothReal_laplacian {δ : ℝ} (hδ : 0 < δ) (Z : ℝ)
    (x : Configuration 1) :
    (∑ k : Coordinate 1, fderiv ℝ
      (fun y => fderiv ℝ (hydrogenSmoothReal Z δ) y (coordinateVector k))
      x (coordinateVector k)) =
      (Z^2 * ‖x‖^2 / (‖x‖^2 + δ) -
        Z * (2*‖x‖^2 + 3*δ) / (Real.sqrt (‖x‖^2 + δ))^3) *
        hydrogenSmoothReal Z δ x := by
  simp_rw [hydrogenSmoothReal_diagonal_second_derivative hδ]
  rw [← Finset.sum_mul]
  congr 1
  have hnorm : (∑ k : Coordinate 1, (x k)^2) = ‖x‖^2 :=
    (EuclideanSpace.real_norm_sq_eq x).symm
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, hnorm, nsmul_eq_mul]
  norm_num
  have hs := Real.sq_sqrt (le_of_lt (hydrogenSmooth_denominator_pos hδ x))
  have hn := (Real.sqrt_pos.2 (hydrogenSmooth_denominator_pos hδ x)).ne'
  have hs3 : (Real.sqrt (‖x‖^2 + δ))^3 = (‖x‖^2 + δ) * Real.sqrt (‖x‖^2 + δ) := by
    rw [pow_succ, hs]
  field_simp
  simp only [hs3, hs]
  ring

theorem hydrogenSmooth_laplacian {δ : ℝ} (hδ : 0 < δ) (Z : ℝ)
    (x : Configuration 1) :
    (∑ k : Coordinate 1, fderiv ℝ
      (fun y => fderiv ℝ (hydrogenSmooth Z δ) y (coordinateVector k))
      x (coordinateVector k)) =
      ((Z^2 * ‖x‖^2 / (‖x‖^2 + δ) -
        Z * (2*‖x‖^2 + 3*δ) / (Real.sqrt (‖x‖^2 + δ))^3 : ℝ) : ℂ) *
        hydrogenSmooth Z δ x := by
  have he (k : Coordinate 1) :
      fderiv ℝ (fun y => fderiv ℝ (hydrogenSmooth Z δ) y (coordinateVector k))
        x (coordinateVector k) =
      (fderiv ℝ (fun y => fderiv ℝ (hydrogenSmoothReal Z δ) y (coordinateVector k))
        x (coordinateVector k) : ℂ) := by
    have hf : (fun y => fderiv ℝ (hydrogenSmooth Z δ) y (coordinateVector k)) =
        fun y => (fderiv ℝ (hydrogenSmoothReal Z δ) y (coordinateVector k) : ℂ) := by
      funext y
      exact hydrogen_fderiv_ofReal ((hydrogenSmoothReal_contDiff hδ Z).differentiable (by simp) y) _
    rw [hf]
    exact hydrogen_fderiv_ofReal
      ((hydrogenSmoothReal_first_contDiff hδ Z k).differentiable (by simp) x) _
  simp_rw [he]
  rw [← Complex.ofReal_sum, hydrogenSmoothReal_laplacian hδ, Complex.ofReal_mul]
  rfl

#print axioms hydrogenSmoothReal_laplacian
#print axioms hydrogenSmooth_laplacian
end TheoremT.Continuum
