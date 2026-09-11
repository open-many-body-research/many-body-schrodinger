import SmoothRealDerivativeSums_v1
import LocalWeakLaplacian_v1

noncomputable section
open scoped ContDiff
namespace TheoremT.Continuum

theorem reflected_real_test_partial {N : ℕ} {φ : Configuration N → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (x y v : Configuration N) :
    fderiv ℝ (fun z => φ (x-z)) y v = -fderiv ℝ φ (x-y) v := by
  have hh := (hφ.differentiable (by simp) (x-y)).hasFDerivAt.comp y
    ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))
  change HasFDerivAt (𝕜 := ℝ) (fun z => φ (x-z)) _ y at hh
  rw [hh.fderiv]
  simp

theorem reflected_real_test_mixed {N : ℕ} {φ : Configuration N → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (x y v w : Configuration N) :
    fderiv ℝ (fun z => fderiv ℝ (fun t => φ (x-t)) z v) y w =
      fderiv ℝ (fun z => fderiv ℝ φ z v) (x-y) w := by
  simp_rw [reflected_real_test_partial hφ]
  have hd : ContDiff ℝ ∞ (fun z => fderiv ℝ φ z v) :=
    (hφ.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  change fderiv ℝ (-(fun z => fderiv ℝ φ (x-z) v)) y w = _
  rw [fderiv_neg]
  simp only [ContinuousLinearMap.neg_apply,reflected_real_test_partial hd,neg_neg]

theorem reflected_real_test_laplacian {N : ℕ} {φ : Configuration N → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (x y : Configuration N) :
    realTestLaplacian (fun z => φ (x-z)) y=realTestLaplacian φ (x-y) := by
  unfold realTestLaplacian
  simp only [reflected_real_test_mixed hφ]

#print axioms reflected_real_test_laplacian
end TheoremT.Continuum
