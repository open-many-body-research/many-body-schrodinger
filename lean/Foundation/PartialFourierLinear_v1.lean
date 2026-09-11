import CompactPartialFourier_v1

noncomputable section
open MeasureTheory
open scoped ContDiff FourierTransform BigOperators
namespace TheoremT.Continuum
variable {Y T : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T]
  [MeasurableSpace T] [BorelSpace T] [FiniteDimensional ℝ T]

theorem partialFourier_integrand_slice_integrable {G : Y × T → ℂ} (hG : Continuous G)
    (hc : HasCompactSupport G) (ξ : T) (y : Y) :
    Integrable (fun t => partialFourierKernel ξ t * G (y,t)) volume :=
  compact_slice_integrable (((partialFourierKernel_contDiff ξ).continuous.comp continuous_snd).mul hG)
    hc.mul_left y

theorem partialFourier_neg (G : Y × T → ℂ) (ξ : T) (y : Y) :
    partialFourier (fun p => -G p) ξ y = -partialFourier G ξ y := by
  simp only [partialFourier,Real.fourier_eq',smul_eq_mul,mul_neg,integral_neg]

theorem partialFourier_y_mul (m : Y → ℂ) (G : Y × T → ℂ) (ξ : T) (y : Y) :
    partialFourier (fun p => m p.1 * G p) ξ y = m y * partialFourier G ξ y := by
  simp only [partialFourier,Real.fourier_eq',smul_eq_mul]
  calc
    _ = ∫ t, m y * (partialFourierKernel ξ t * G (y,t)) := by
      apply integral_congr_ae
      filter_upwards [] with t
      change partialFourierKernel ξ t * (m y * G (y,t)) = _
      ring
    _ = _ := integral_const_mul _ _

theorem partialFourier_add {G H : Y × T → ℂ} (hG : Continuous G) (hcG : HasCompactSupport G)
    (hH : Continuous H) (hcH : HasCompactSupport H) (ξ : T) (y : Y) :
    partialFourier (fun p => G p + H p) ξ y = partialFourier G ξ y + partialFourier H ξ y := by
  simp only [partialFourier,Real.fourier_eq',smul_eq_mul,mul_add]
  exact integral_add (partialFourier_integrand_slice_integrable hG hcG ξ y)
    (partialFourier_integrand_slice_integrable hH hcH ξ y)

theorem partialFourier_finset_sum {ι : Type*} (s : Finset ι) (G : ι → Y × T → ℂ)
    (hG : ∀ i ∈ s, Continuous (G i)) (hcG : ∀ i ∈ s, HasCompactSupport (G i)) (ξ : T) (y : Y) :
    partialFourier (fun p => ∑ i ∈ s, G i p) ξ y = ∑ i ∈ s, partialFourier (G i) ξ y := by
  simp only [partialFourier,Real.fourier_eq',smul_eq_mul,Finset.mul_sum]
  exact integral_finsetSum _ (fun i hi => partialFourier_integrand_slice_integrable (hG i hi) (hcG i hi) ξ y)

#print axioms partialFourier_neg
#print axioms partialFourier_y_mul
#print axioms partialFourier_add
#print axioms partialFourier_finset_sum
end TheoremT.Continuum
