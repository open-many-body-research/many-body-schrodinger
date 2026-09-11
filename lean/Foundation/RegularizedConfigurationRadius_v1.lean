import SmoothConfigurationRadiusSecond_v1

/-! Positive regularization of the actual configuration radius. This is the
smooth local building block for the physical Coulomb cusp factor. -/
noncomputable section
open scoped ContDiff BigOperators
namespace TheoremT.Continuum

def regularizedConfigurationRadius (N : ℕ) (δ : ℝ) (x : Configuration N) : ℝ :=
  Real.sqrt (‖x‖^2+δ)

theorem regularizedConfigurationRadius_pos {N : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (x : Configuration N) : 0 < regularizedConfigurationRadius N δ x :=
  Real.sqrt_pos.mpr (by positivity)

theorem regularizedConfigurationRadius_sq {N : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (x : Configuration N) : (regularizedConfigurationRadius N δ x)^2 = ‖x‖^2+δ :=
  Real.sq_sqrt (by positivity)

theorem norm_le_regularizedConfigurationRadius {N : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (x : Configuration N) : ‖x‖ ≤ regularizedConfigurationRadius N δ x := by
  nlinarith [regularizedConfigurationRadius_sq hδ x,
    regularizedConfigurationRadius_pos hδ x,norm_nonneg x]

theorem regularizedConfigurationRadius_contDiff (N : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ContDiff ℝ ∞ (regularizedConfigurationRadius N δ) :=
  ((contDiff_norm_sq ℝ).add contDiff_const).sqrt (fun x => by positivity)

theorem regularizedConfigurationRadius_partial {N : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (x : Configuration N) (k : Coordinate N) :
    fderiv ℝ (regularizedConfigurationRadius N δ) x (coordinateVector k) =
      x k/regularizedConfigurationRadius N δ x := by
  have hh := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.add_const δ).sqrt
    (by positivity : ‖x‖^2+δ ≠ 0)
  change HasFDerivAt (regularizedConfigurationRadius N δ) _ x at hh
  rw [hh.fderiv]
  have hi : inner ℝ x (coordinateVector k) = x k := by
    simp [coordinateVector,EuclideanSpace.inner_single_right]
  simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.add_apply,
    innerSL_apply_apply,smul_eq_mul,two_smul]
  rw [hi]
  unfold regularizedConfigurationRadius
  ring

theorem regularizedConfigurationRadius_gradient_sq_le_one {N : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (x : Configuration N) :
    (∑ k : Coordinate N, (fderiv ℝ (regularizedConfigurationRadius N δ) x (coordinateVector k))^2) ≤ 1 := by
  simp only [regularizedConfigurationRadius_partial hδ,div_pow,← Finset.sum_div,
    ← EuclideanSpace.real_norm_sq_eq,regularizedConfigurationRadius_sq hδ]
  exact (div_le_one (by positivity)).mpr (by linarith)

theorem regularizedConfigurationRadius_partial_abs_le_one {N : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (x : Configuration N) (k : Coordinate N) :
    |fderiv ℝ (regularizedConfigurationRadius N δ) x (coordinateVector k)| ≤ 1 := by
  have hs := Finset.single_le_sum (fun i _ => sq_nonneg
    (fderiv ℝ (regularizedConfigurationRadius N δ) x (coordinateVector i))) (Finset.mem_univ k)
  have h := regularizedConfigurationRadius_gradient_sq_le_one hδ x
  rw [abs_le]
  constructor <;> nlinarith

#print axioms regularizedConfigurationRadius_partial
#print axioms regularizedConfigurationRadius_gradient_sq_le_one
end TheoremT.Continuum
