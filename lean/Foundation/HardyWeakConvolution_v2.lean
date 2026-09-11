import HardyWeakConvolution_v1
import HardyWeakCutoff_v2

/-! Compact mollification of L² cutoffs, handling representatives by a.e.
equality rather than assuming an L² quotient representative has compact support. -/
noncomputable section
open MeasureTheory
open scoped ContDiff Convolution
namespace TheoremT.Continuum

theorem mollify_cutoff_compact {N : ℕ} (η χ : Configuration N → ℝ)
    (hcη : HasCompactSupport η) (hχ : Continuous χ) (hcχ : HasCompactSupport χ)
    (f : SpatialL2 N) : HasCompactSupport (mollify η (cutoffMul χ hχ hcχ f)) := by
  let L : ℂ →L[ℝ] ℝ →L[ℝ] ℂ :=
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ).flip
  have he : mollify η (cutoffMul χ hχ hcχ f) =
      ((fun y => χ y • f y) ⋆[L, volume] η) := by
    funext x
    apply integral_congr_ae
    filter_upwards [cutoffMul_ae χ hχ hcχ f] with y hy
    change η (x-y) • cutoffMul χ hχ hcχ f y = η (x-y) • (χ y • f y)
    rw [hy]
  rw [he]
  exact hcχ.smul_right.convolution L hcη

/-- An explicitly specified smooth compact function, for every original L²
input; no pointwise support property is required of its chosen representative. -/
theorem mollify_cutoff_smooth_compact {N : ℕ} (η χ : Configuration N → ℝ)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hχ : Continuous χ) (hcχ : HasCompactSupport χ) (f : SpatialL2 N) :
    ContDiff ℝ ∞ (mollify η (cutoffMul χ hχ hcχ f)) ∧
      HasCompactSupport (mollify η (cutoffMul χ hχ hcχ f)) :=
  ⟨mollify_contDiff η hη hcη _, mollify_cutoff_compact η χ hcη hχ hcχ f⟩

theorem mollify_cutoff_derivative {N : ℕ} {f g : SpatialL2 N} {k : Coordinate N}
    (hg : WeakPartial f g k) (η χ : Configuration N → ℝ)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (x : Configuration N) :
    fderiv ℝ (mollify η (cutoffMul χ hχ.continuous hcχ f)) x (coordinateVector k) =
      mollify η (cutoffMul χ hχ.continuous hcχ g +
        cutoffMul (fun y => fderiv ℝ χ y (coordinateVector k))
          ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const)
          (hcχ.fderiv_apply ℝ (coordinateVector k)) f) x :=
  mollify_derivative (weakPartial_cutoff hg χ hχ hcχ) η hη hcη x

#print axioms mollify_cutoff_compact
#print axioms mollify_cutoff_smooth_compact
#print axioms mollify_cutoff_derivative
end TheoremT.Continuum
