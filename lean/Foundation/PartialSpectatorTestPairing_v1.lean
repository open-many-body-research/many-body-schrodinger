import PartialSpectatorPairingIntegrable_v1

noncomputable section
open MeasureTheory MeasureTheory.Measure
namespace TheoremT.Continuum
variable {Y T F : Type*}
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y] {μ : Measure Y} [IsAddHaarMeasure μ]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T]
  [MeasurableSpace T] [BorelSpace T] {ν : Measure T} [IsAddHaarMeasure ν]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem partial_spectator_pairing_translate
    (K : T → ℝ) (G : Y × T → F) (φ : Y × T → ℝ) (s : T) :
    (∫ p, φ p • (K s • G (p.1,p.2-s)) ∂μ.prod ν) =
      K s • (∫ p, φ (p.1,p.2+s) • G p ∂μ.prod ν) := by
  let e : Y × T ≃ₜ Y × T := (Homeomorph.refl Y).prodCongr (Homeomorph.addRight s)
  have hp : MeasurePreserving e (μ.prod ν) (μ.prod ν) :=
    (MeasurePreserving.id μ).prod (measurePreserving_add_right ν s)
  have he := hp.integral_comp e.measurableEmbedding
    (fun p => φ p • (K s • G (p.1,p.2-s)))
  have hval (p : Y × T) : e p = (p.1,p.2+s) := rfl
  simp only [hval,add_sub_cancel_right] at he
  rw [← he,← integral_smul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun p => smul_comm (φ (p.1,p.2+s)) (K s) (G p))

theorem partialSpectatorConvolution_test_pairing
    {K : T → ℝ} {G : Y × T → F} {φ : Y × T → ℝ}
    (hK : StronglyMeasurable K) (hKi : Integrable K ν)
    (hG : StronglyMeasurable G) (hG2 : MemLp G 2 (μ.prod ν))
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) :
    (∫ p, φ p • partialSpectatorConvolution (ν := ν) K G p ∂μ.prod ν) =
      ∫ s, K s • (∫ p, φ (p.1,p.2+s) • G p ∂μ.prod ν) ∂ν := by
  have hi := partialSpectatorConvolution_test_integrable_product hK hKi hG hG2 hφ hcφ
  calc
    _ = ∫ p, ∫ s, φ p • (K s • G (p.1,p.2-s)) ∂ν ∂μ.prod ν := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun p => (integral_smul (φ p) _).symm)
    _ = ∫ s, ∫ p, φ p • (K s • G (p.1,p.2-s)) ∂μ.prod ν ∂ν := integral_integral_swap hi
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall
      (fun s => partial_spectator_pairing_translate K G φ s))

#print axioms partial_spectator_pairing_translate
#print axioms partialSpectatorConvolution_test_pairing
end TheoremT.Continuum
