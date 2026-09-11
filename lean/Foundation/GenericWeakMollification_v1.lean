import GenericWeakEllipticGain_v1
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-! Kernel testing and actual smooth mollification of the project's weak
derivatives. No Sobolev approximation or convolution L² contraction is assumed. -/
noncomputable section
open MeasureTheory
open scoped ContDiff Convolution
namespace TheoremT.Continuum.GenericMollifier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def mollify (η : E → ℝ) (f : Lp ℂ 2 (volume : Measure E))
    (x : E) : ℂ := ∫ y, η (x - y) • f y

theorem weakDirectional_kernel_test {f g : Lp ℂ 2 (volume : Measure E)} {v : E}
    (hg : WeakL2Directional f g v) (η : E → ℝ)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (x : E) :
    (∫ y, η (x - y) • g y) =
      (∫ y, fderiv ℝ η (x - y) v • f y) := by
  have ht : ContDiff ℝ ∞ (fun y => η (x - y)) :=
    hη.comp (contDiff_const.sub contDiff_id)
  have hct : HasCompactSupport (fun y => η (x - y)) :=
    hcη.comp_homeomorph (Homeomorph.subLeft x)
  have hder (y : E) :
      fderiv ℝ (fun z => η (x - z)) y v =
        -(fderiv ℝ η (x - y) v) := by
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

theorem mollify_contDiff (η : E → ℝ)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (f : Lp ℂ 2 (volume : Measure E)) :
    ContDiff ℝ ∞ (mollify η f) := by
  change ContDiff ℝ ∞ ((f : E → ℂ) ⋆[mollifyPairing, volume] η)
  exact hcη.contDiff_convolution_right mollifyPairing
    ((Lp.memLp f).locallyIntegrable (by norm_num)) hη

theorem mollify_derivative {f g : Lp ℂ 2 (volume : Measure E)} {v : E}
    (hg : WeakL2Directional f g v) (η : E → ℝ)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (x : E) :
    fderiv ℝ (mollify η f) x v = mollify η g x := by
  have hf := (Lp.memLp f).locallyIntegrable (by norm_num)
  have hη1 : ContDiff ℝ 1 η := hη.of_le (by simp)
  have hd := hcη.hasFDerivAt_convolution_right mollifyPairing hf hη1 x
  change HasFDerivAt (𝕜 := ℝ) (mollify η f) _ x at hd
  rw [hd.fderiv]
  rw [convolution_def]
  rw [ContinuousLinearMap.integral_apply]
  · change (∫ y, fderiv ℝ η (x-y) v • f y) = mollify η g x
    exact (weakDirectional_kernel_test hg η hη hcη x).symm
  · exact (hcη.fderiv ℝ).convolutionExists_right
      (mollifyPairing.precompR (E)) hf
      (hη.continuous_fderiv (by simp)) x

#print axioms weakDirectional_kernel_test
#print axioms mollify_contDiff
#print axioms mollify_derivative
end TheoremT.Continuum.GenericMollifier
