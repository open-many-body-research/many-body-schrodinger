import LocalWeakLaplacian_v1

noncomputable section
open scoped ContDiff
namespace TheoremT.Continuum

theorem realTestLaplacian_contDiff {N : ℕ} {φ : Configuration N → ℝ}
    (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (realTestLaplacian φ) := by
  apply ContDiff.sum
  intro k hk
  have hd : ContDiff ℝ ∞ (fun y => fderiv ℝ φ y (coordinateVector k)) :=
    (hφ.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  exact (hd.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const

#print axioms realTestLaplacian_contDiff
end TheoremT.Continuum
