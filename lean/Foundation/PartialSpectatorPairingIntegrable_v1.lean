import PartialSpectatorSmoothKernel_v1

noncomputable section
open MeasureTheory MeasureTheory.Measure
namespace TheoremT.Continuum
variable {Y T F : Type*}
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y] {μ : Measure Y} [IsAddHaarMeasure μ]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T]
  [MeasurableSpace T] [BorelSpace T] {ν : Measure T} [IsAddHaarMeasure ν]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem partialSpectatorConvolution_test_integrable_product
    {K : T → ℝ} {G : Y × T → F} {φ : Y × T → ℝ}
    (hK : StronglyMeasurable K) (hKi : Integrable K ν)
    (hG : StronglyMeasurable G) (hG2 : MemLp G 2 (μ.prod ν))
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) :
    Integrable (fun q : (Y × T) × T => φ q.1 • (K q.2 • G (q.1.1,q.1.2-q.2)))
      ((μ.prod ν).prod ν) := by
  have hM : StronglyMeasurable (fun q : (Y × T) × T => φ q.1 • (K q.2 • G (q.1.1,q.1.2-q.2))) :=
    (hφ.stronglyMeasurable.comp_measurable measurable_fst).smul
      (partialSpectatorConvolution_integrand_stronglyMeasurable hK hG)
  apply (integrable_prod_iff hM.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [partialSpectatorConvolution_ae_integrable hKi hG2] with p hp
    exact hp.smul (φ p)
  · have hN := partialSpectatorConvolution_ae_memLp_two hKi.norm hG2.norm
    have ht := (hN.locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
      hφ.norm hcφ.norm
    have he (p : Y × T) :
        (∫ s, ‖φ p • (K s • G (p.1,p.2-s))‖ ∂ν) =
          ‖φ p‖ * partialSpectatorConvolution (ν := ν) (fun s => ‖K s‖) (fun q => ‖G q‖) p := by
      simp only [norm_smul,partialSpectatorConvolution,smul_eq_mul]
      rw [← integral_const_mul]
    simpa only [smul_eq_mul,he] using ht

#print axioms partialSpectatorConvolution_test_integrable_product
end TheoremT.Continuum
