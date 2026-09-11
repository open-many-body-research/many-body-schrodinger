import HardyWeakConvolution_v2
import HardyConvolutionNormalized_v1

noncomputable section
open MeasureTheory
open scoped ContDiff Convolution
namespace TheoremT.Continuum

theorem mollify_eq_normalized_orientation {N : ℕ} (η : Configuration N → ℝ)
    (f : SpatialL2 N) :
    mollify η f = (fun x => ∫ t, η t • f (x-t)) := by
  change ((f : Configuration N → ℂ) ⋆[
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ).flip, volume] η) =
    (η ⋆[(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ), volume]
      (f : Configuration N → ℂ))
  exact convolution_flip (f := η) (g := (f : Configuration N → ℂ))
    (L := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ)) (μ := volume)

/-- Actual Lebesgue L² contraction of the mollifier used in the weak-derivative
construction; all strongly-measurable representative obligations are discharged. -/
theorem mollify_memLp_two_and_bound {N : ℕ} (η : Configuration N → ℝ)
    (hηm : Measurable η) (hηn : ∀ x, 0 ≤ η x) (hηi : Integrable η volume)
    (hηone : (∫ x, η x) = 1) (f : SpatialL2 N) :
    MemLp (mollify η f) 2 volume ∧
      (∫ x, ‖mollify η f x‖^2) ≤ (∫ x, ‖f x‖^2) := by
  rw [mollify_eq_normalized_orientation]
  exact TheoremT.HardyConvolution.normalized_convolution_memLp_two_and_bound
    hηm hηn hηi hηone (Lp.stronglyMeasurable f) (Lp.memLp f)

/-- Smoothing an existing actual weak derivative never increases its L² energy
when the real smooth kernel is nonnegative and normalized. -/
theorem mollify_derivative_memLp_two_and_bound {N : ℕ}
    {f g : SpatialL2 N} {k : Coordinate N} (hg : WeakPartial f g k)
    (η : Configuration N → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hηn : ∀ x, 0 ≤ η x) (hηone : (∫ x, η x) = 1) :
    MemLp (fun x => fderiv ℝ (mollify η f) x (coordinateVector k)) 2 volume ∧
      (∫ x, ‖fderiv ℝ (mollify η f) x (coordinateVector k)‖^2) ≤
        (∫ x, ‖g x‖^2) := by
  simp_rw [mollify_derivative hg η hη hcη]
  exact mollify_memLp_two_and_bound η hη.continuous.measurable hηn
    (hη.continuous.integrable_of_hasCompactSupport hcη) hηone g

#print axioms mollify_eq_normalized_orientation
#print axioms mollify_memLp_two_and_bound
#print axioms mollify_derivative_memLp_two_and_bound
end TheoremT.Continuum
