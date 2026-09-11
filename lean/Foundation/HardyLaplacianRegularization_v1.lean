import HardyLaplacianCore_v3
import HardyWeakConvolution_v3
import MollifierSequence_v2
import CutoffH2Convergence_v2

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace TheoremT.Continuum

theorem smoothPartial_mollify {N : ℕ} {f g : SpatialL2 N} {k : Coordinate N}
    (hg : WeakPartial f g k) (η : Configuration N → ℝ)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) :
    smoothPartial (mollify η f) k = mollify η g := by
  funext x
  exact mollify_derivative hg η hη hcη x

theorem smoothSecond_mollify {N : ℕ} {f dk e : SpatialL2 N} {k l : Coordinate N}
    (hd : WeakPartial f dk k) (he : WeakPartial dk e l) (η : Configuration N → ℝ)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) :
    smoothPartial (smoothPartial (mollify η f) k) l = mollify η e := by
  rw [smoothPartial_mollify hd η hη hcη]
  exact smoothPartial_mollify he η hη hcη

theorem smoothLaplacian_mollify {N : ℕ} {f : SpatialL2 N}
    (d : Coordinate N → SpatialL2 N) (e : Coordinate N → Coordinate N → SpatialL2 N)
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k l, WeakPartial (d k) (e k l) l)
    (η : Configuration N → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (x : Configuration N) :
    smoothLaplacian (mollify η f) x = ∑ k : Coordinate N, mollify η (e k k) x := by
  unfold smoothLaplacian
  exact Finset.sum_congr rfl (fun k _ => congrFun
    (smoothSecond_mollify (hd k) (he k k) η hη hcη) x)

theorem mollifyKernel_cutoff_contDiff_compact {N : ℕ} (n m : ℕ) (f : SpatialL2 N) :
    ContDiff ℝ ∞ (mollify (mollifierKernel N m) (cutoffAt n f)) ∧
      HasCompactSupport (mollify (mollifierKernel N m) (cutoffAt n f)) := by
  exact mollify_cutoff_smooth_compact (mollifierKernel N m)
    (scaledCutoff N ((n : ℝ)+1)) (mollifierKernel_contDiff N m)
    (mollifierKernel_hasCompactSupport N m) (scaledCutoff_contDiff N _).continuous
    (scaledCutoff_hasCompactSupport N (by positivity)) f

#print axioms smoothSecond_mollify
#print axioms mollifyKernel_cutoff_contDiff_compact
end TheoremT.Continuum
