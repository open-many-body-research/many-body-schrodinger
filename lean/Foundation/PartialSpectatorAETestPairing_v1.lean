import PartialSpectatorTestPairing_v1

noncomputable section
open MeasureTheory MeasureTheory.Measure
namespace TheoremT.Continuum
variable {Y T F : Type*}
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y] {μ : Measure Y} [IsAddHaarMeasure μ]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T]
  [MeasurableSpace T] [BorelSpace T] {ν : Measure T} [IsAddHaarMeasure ν]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem partialSpectatorConvolution_ae_test_pairing
    {K : T → ℝ} {G : Y × T → F} {φ : Y × T → ℝ}
    (hKi : Integrable K ν) (hG2 : MemLp G 2 (μ.prod ν))
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) :
    (∫ p, φ p • partialSpectatorConvolution (ν := ν) K G p ∂μ.prod ν) =
      ∫ s, K s • (∫ p, φ (p.1,p.2+s) • G p ∂μ.prod ν) ∂ν := by
  have hk := hKi.aestronglyMeasurable.ae_eq_mk
  have hg := hG2.aestronglyMeasurable.ae_eq_mk
  have hpair := partialSpectatorConvolution_test_pairing
    hKi.aestronglyMeasurable.stronglyMeasurable_mk (hKi.congr hk)
    hG2.aestronglyMeasurable.stronglyMeasurable_mk (hG2.ae_eq hg) hφ hcφ
  have hl : (∫ p, φ p • partialSpectatorConvolution (ν := ν) K G p ∂μ.prod ν) =
      ∫ p, φ p • partialSpectatorConvolution (ν := ν) (hKi.aestronglyMeasurable.mk K)
        (hG2.aestronglyMeasurable.mk G) p ∂μ.prod ν := by
    rw [partialSpectatorConvolution_kernel_congr hk G]
    apply integral_congr_ae
    filter_upwards [partialSpectatorConvolution_ae_congr_of_ae
      (K := hKi.aestronglyMeasurable.mk K) hg] with p hp
    rw [hp]
  have hr : (∫ s, K s • (∫ p, φ (p.1,p.2+s) • G p ∂μ.prod ν) ∂ν) =
      ∫ s, hKi.aestronglyMeasurable.mk K s •
        (∫ p, φ (p.1,p.2+s) • hG2.aestronglyMeasurable.mk G p ∂μ.prod ν) ∂ν := by
    apply integral_congr_ae
    filter_upwards [hk] with s hs
    rw [hs]
    congr 1
    apply integral_congr_ae
    filter_upwards [hg] with p hp
    rw [hp]
  rw [hl,hr]
  exact hpair

#print axioms partialSpectatorConvolution_ae_test_pairing
end TheoremT.Continuum
