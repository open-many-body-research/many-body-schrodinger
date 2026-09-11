import CompactInnerCoordinate_v1

noncomputable section
open MeasureTheory
open scoped ContDiff RealInnerProductSpace
namespace TheoremT.Continuum
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem cutoff_directional_product {η : E → ℝ} {u : E → F}
    (hη : ContDiff ℝ ∞ η) (hu : ContDiff ℝ ∞ u) (x v : E) :
    fderiv ℝ (fun y => η y • u y) x v =
      (fderiv ℝ η x v) • u x + η x • fderiv ℝ u x v := by
  have h := ((hη.differentiable (by simp) x).hasFDerivAt).smul
    (hu.differentiable (by simp) x).hasFDerivAt
  simpa only [Pi.smul_def', ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, add_comm] using
    congrArg (fun L : E →L[ℝ] F => L v) h.fderiv

theorem cutoff_square_directional_product {η : E → ℝ} {u : E → F}
    (hη : ContDiff ℝ ∞ η) (hu : ContDiff ℝ ∞ u) (x v : E) :
    fderiv ℝ (fun y => (η y)^2 • u y) x v =
      (2*η x*fderiv ℝ η x v) • u x + (η x)^2 • fderiv ℝ u x v := by
  rw [cutoff_directional_product (hη.pow 2) hu]
  have h := ((hη.differentiable (by simp) x).hasFDerivAt).pow 2
  have he := congrArg (fun L : E →L[ℝ] ℝ => L v) h.fderiv
  simp only [ContinuousLinearMap.smul_apply,smul_eq_mul,Nat.reduceSub,pow_one,Nat.cast_ofNat] at he
  rw [he]
  norm_num only [nsmul_eq_mul, Nat.cast_ofNat]

theorem cutoff_directional_norm_square {η : E → ℝ} {u : E → F}
    (hη : ContDiff ℝ ∞ η) (hu : ContDiff ℝ ∞ u) (x v : E) :
    ‖fderiv ℝ (fun y => η y • u y) x v‖^2 =
      ‖η x • fderiv ℝ u x v‖^2 +
      2*inner ℝ ((fderiv ℝ η x v) • u x) (η x • fderiv ℝ u x v) +
      ‖(fderiv ℝ η x v) • u x‖^2 := by
  rw [cutoff_directional_product hη hu,norm_add_sq_real]
  ring

theorem cutoff_square_directional_inner {η : E → ℝ} {u : E → F}
    (hη : ContDiff ℝ ∞ η) (hu : ContDiff ℝ ∞ u) (x v : E) :
    inner ℝ (fderiv ℝ (fun y => (η y)^2 • u y) x v) (fderiv ℝ u x v) =
      ‖η x • fderiv ℝ u x v‖^2 +
      2*inner ℝ ((fderiv ℝ η x v) • u x) (η x • fderiv ℝ u x v) := by
  rw [cutoff_square_directional_product hη hu]
  simp only [inner_add_left,real_inner_smul_left,real_inner_smul_right,
    real_inner_self_eq_norm_sq,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
  ring

#print axioms cutoff_directional_product
#print axioms cutoff_square_directional_product
#print axioms cutoff_directional_norm_square
#print axioms cutoff_square_directional_inner
end TheoremT.Continuum
