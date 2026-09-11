import HardyLaplacianCore_v2
import LocalWeakLaplacian_v1

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum

theorem smoothPartial_real_projection {N : ℕ} (L : ℂ →L[ℝ] ℝ)
    {φ : Configuration N → ℂ} (hφ : ContDiff ℝ ∞ φ) (x : Configuration N) (k : Coordinate N) :
    fderiv ℝ (fun y => L (φ y)) x (coordinateVector k) = L (smoothPartial φ k x) := by
  have hd := L.hasFDerivAt.comp x ((hφ.differentiable (by simp)) x).hasFDerivAt
  change fderiv ℝ (L ∘ φ) x (coordinateVector k) = _
  rw [hd.fderiv]
  rfl

theorem smoothLaplacian_real_projection {N : ℕ} (L : ℂ →L[ℝ] ℝ)
    {φ : Configuration N → ℂ} (hφ : ContDiff ℝ ∞ φ) (x : Configuration N) :
    realTestLaplacian (fun y => L (φ y)) x = L (smoothLaplacian φ x) := by
  unfold realTestLaplacian smoothLaplacian
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have he : (fun y => fderiv ℝ (fun z => L (φ z)) y (coordinateVector k)) =
      (fun y => L (smoothPartial φ k y)) := by
    funext y
    exact smoothPartial_real_projection L hφ y k
  rw [he]
  exact smoothPartial_real_projection L (smoothPartial_contDiff hφ k) x k

#print axioms smoothLaplacian_real_projection
end TheoremT.Continuum
