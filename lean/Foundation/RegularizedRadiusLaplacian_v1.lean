import RegularizedRadiusHessian_v1

noncomputable section
open Filter
open scoped ContDiff BigOperators Topology
namespace TheoremT.Continuum

theorem regularizedConfigurationRadius_hessian_formula {N : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (x : Configuration N) (k l : Coordinate N) :
    fderiv ℝ (fun y => fderiv ℝ (regularizedConfigurationRadius N δ) y (coordinateVector k))
      x (coordinateVector l) =
      (coordinateVector l k)/regularizedConfigurationRadius N δ x -
        x k*x l/(regularizedConfigurationRadius N δ x)^3 := by
  rw [regularizedConfigurationRadius_mixed_partial hδ]
  ring

theorem regularizedConfigurationRadius_laplacian {N : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (x : Configuration N) :
    (∑ k : Coordinate N, fderiv ℝ
      (fun y => fderiv ℝ (regularizedConfigurationRadius N δ) y (coordinateVector k))
      x (coordinateVector k)) =
      (3*N:ℝ)/regularizedConfigurationRadius N δ x-
        ‖x‖^2/(regularizedConfigurationRadius N δ x)^3 := by
  simp_rw [regularizedConfigurationRadius_hessian_formula hδ]
  have hk (k : Coordinate N) : coordinateVector k k = 1 := by simp [coordinateVector]
  simp_rw [hk]
  simp only [one_div,
    Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,
    nsmul_eq_mul,← Finset.sum_div,← pow_two,← EuclideanSpace.real_norm_sq_eq]
  push_cast
  ring

theorem regularizedConfigurationRadius_tendsto {N : ℕ} {δ : ℕ → ℝ}
    (hδ : Tendsto δ atTop (𝓝 0)) (x : Configuration N) :
    Tendsto (fun n => regularizedConfigurationRadius N (δ n) x) atTop (𝓝 ‖x‖) := by
  convert! (hδ.const_add (‖x‖^2)).sqrt using 1
  simp [Real.sqrt_sq (norm_nonneg x)]

theorem regularizedConfigurationRadius_partial_tendsto {N : ℕ} {δ : ℕ → ℝ}
    (hp : ∀ n, 0 < δ n) (hδ : Tendsto δ atTop (𝓝 0))
    {x : Configuration N} (hx : x ≠ 0) (k : Coordinate N) :
    Tendsto (fun n => fderiv ℝ (regularizedConfigurationRadius N (δ n)) x (coordinateVector k))
      atTop (𝓝 (x k/‖x‖)) := by
  simp_rw [regularizedConfigurationRadius_partial (hp _)]
  exact tendsto_const_nhds.div (regularizedConfigurationRadius_tendsto hδ x) (norm_ne_zero_iff.mpr hx)

theorem regularizedConfigurationRadius_hessian_tendsto {N : ℕ} {δ : ℕ → ℝ}
    (hp : ∀ n, 0 < δ n) (hδ : Tendsto δ atTop (𝓝 0))
    {x : Configuration N} (hx : x ≠ 0) (k l : Coordinate N) :
    Tendsto (fun n => fderiv ℝ (fun y => fderiv ℝ (regularizedConfigurationRadius N (δ n))
      y (coordinateVector k)) x (coordinateVector l)) atTop
      (𝓝 ((coordinateVector l k)/‖x‖-x k*x l/‖x‖^3)) := by
  simp_rw [regularizedConfigurationRadius_hessian_formula (hp _)]
  have ht := regularizedConfigurationRadius_tendsto hδ x
  exact (tendsto_const_nhds.div ht (norm_ne_zero_iff.mpr hx)).sub
    (tendsto_const_nhds.div (ht.pow 3) (pow_ne_zero _ (norm_ne_zero_iff.mpr hx)))

theorem regularized_oneElectron_radius_laplacian_tendsto {δ : ℕ → ℝ}
    (hp : ∀ n, 0 < δ n) (hδ : Tendsto δ atTop (𝓝 0))
    {x : Configuration 1} (hx : x ≠ 0) :
    Tendsto (fun n => ∑ k : Coordinate 1, fderiv ℝ
      (fun y => fderiv ℝ (regularizedConfigurationRadius 1 (δ n)) y (coordinateVector k))
      x (coordinateVector k)) atTop (𝓝 (2/‖x‖)) := by
  simp_rw [regularizedConfigurationRadius_laplacian (hp _)]
  have ht := regularizedConfigurationRadius_tendsto hδ x
  have h : Tendsto (fun n => 3/regularizedConfigurationRadius 1 (δ n) x-
      ‖x‖^2/(regularizedConfigurationRadius 1 (δ n) x)^3) atTop
      (𝓝 (3/‖x‖-‖x‖^2/‖x‖^3)) :=
    (tendsto_const_nhds.div ht (norm_ne_zero_iff.mpr hx)).sub
      (tendsto_const_nhds.div (ht.pow 3) (pow_ne_zero _ (norm_ne_zero_iff.mpr hx)))
  norm_num only [Nat.cast_one,mul_one]
  convert h using 1
  congr 1
  have hn := norm_ne_zero_iff.mpr hx
  field_simp
  <;> ring

#print axioms regularizedConfigurationRadius_laplacian
#print axioms regularized_oneElectron_radius_laplacian_tendsto
end TheoremT.Continuum
