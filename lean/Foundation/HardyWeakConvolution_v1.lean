import HardyWeakCore_v1
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-! Kernel testing and actual smooth mollification of the project's weak
derivatives. No Sobolev approximation or convolution L² contraction is assumed. -/
noncomputable section
open MeasureTheory
open scoped ContDiff Convolution
namespace TheoremT.Continuum

def mollify {N : ℕ} (η : Configuration N → ℝ) (f : SpatialL2 N)
    (x : Configuration N) : ℂ := ∫ y, η (x - y) • f y

theorem weakPartial_kernel_test {N : ℕ} {f g : SpatialL2 N} {k : Coordinate N}
    (hg : WeakPartial f g k) (η : Configuration N → ℝ)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (x : Configuration N) :
    (∫ y, η (x - y) • g y) =
      (∫ y, fderiv ℝ η (x - y) (coordinateVector k) • f y) := by
  have ht : ContDiff ℝ ∞ (fun y => η (x - y)) :=
    hη.comp (contDiff_const.sub contDiff_id)
  have hct : HasCompactSupport (fun y => η (x - y)) :=
    hcη.comp_homeomorph (Homeomorph.subLeft x)
  have hder (y : Configuration N) :
      fderiv ℝ (fun z => η (x - z)) y (coordinateVector k) =
        -(fderiv ℝ η (x - y) (coordinateVector k)) := by
    have hh := (hη.differentiable (by simp) (x-y)).hasFDerivAt.comp y
      ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))
    change HasFDerivAt (𝕜 := ℝ) (fun z => η (x-z)) _ y at hh
    rw [hh.fderiv]
    simp
  have hh := hg (fun y => η (x-y)) ht hct
  simp_rw [hder, neg_smul, integral_neg, neg_neg] at hh
  exact hh

private def mollifyPairing : ℂ →L[ℝ] ℝ →L[ℝ] ℂ :=
  (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ).flip

theorem mollify_contDiff {N : ℕ} (η : Configuration N → ℝ)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (f : SpatialL2 N) :
    ContDiff ℝ ∞ (mollify η f) := by
  change ContDiff ℝ ∞ ((f : Configuration N → ℂ) ⋆[mollifyPairing, volume] η)
  exact hcη.contDiff_convolution_right mollifyPairing
    ((Lp.memLp f).locallyIntegrable (by norm_num)) hη

theorem mollify_derivative {N : ℕ} {f g : SpatialL2 N} {k : Coordinate N}
    (hg : WeakPartial f g k) (η : Configuration N → ℝ)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (x : Configuration N) :
    fderiv ℝ (mollify η f) x (coordinateVector k) = mollify η g x := by
  have hf := (Lp.memLp f).locallyIntegrable (by norm_num)
  have hη1 : ContDiff ℝ 1 η := hη.of_le (by simp)
  have hd := hcη.hasFDerivAt_convolution_right mollifyPairing hf hη1 x
  change HasFDerivAt (𝕜 := ℝ) (mollify η f) _ x at hd
  rw [hd.fderiv]
  rw [convolution_def]
  rw [ContinuousLinearMap.integral_apply]
  · change (∫ y, fderiv ℝ η (x-y) (coordinateVector k) • f y) = mollify η g x
    exact (weakPartial_kernel_test hg η hη hcη x).symm
  · exact (hcη.fderiv ℝ).convolutionExists_right
      (mollifyPairing.precompR (Configuration N)) hf
      (hη.continuous_fderiv (by simp)) x

#print axioms weakPartial_kernel_test
#print axioms mollify_contDiff
#print axioms mollify_derivative
end TheoremT.Continuum
