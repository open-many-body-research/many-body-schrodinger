import GenericSchwartzCutoffPairing_v1
import GenericCompactLaplacianTests_v1

set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Filter TemperedDistribution
open scoped SchwartzMap Laplacian LineDeriv ContDiff Topology BigOperators
namespace TheoremT.Continuum
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem generic_schwartz_cutoff_first_pairing_limit
    (φ : 𝓢(E,ℂ)) (f : Lp ℂ 2 (volume : Measure E)) (v : E) :
    Tendsto (fun n : ℕ => ∫ x,
      fderiv ℝ (fun z => genericScaledCutoff E ((n : ℝ)+1) z • φ z) x v * f x)
      atTop (𝓝 (∫ x, fderiv ℝ φ x v * f x)) := by
  have h0 := generic_schwartz_lp_product_integrable φ f
  have h1 : Integrable (fun x => fderiv ℝ φ x v * f x) volume := by
    simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv] using
      generic_schwartz_lp_product_integrable (∂_{v} φ) f
  have ht0 := generic_cutoff_first_integral_limit h0 v
  have ht1 := generic_cutoff_integral_limit h1
  have he (n : ℕ) :
      (∫ x, fderiv ℝ (fun z => genericScaledCutoff E ((n : ℝ)+1) z • φ z) x v * f x) =
      (∫ x, fderiv ℝ (genericScaledCutoff E ((n : ℝ)+1)) x v • (φ x*f x)) +
      (∫ x, genericScaledCutoff E ((n : ℝ)+1) x • (fderiv ℝ φ x v*f x)) := by
    let χ := genericScaledCutoff E ((n : ℝ)+1)
    have hχ : ContDiff ℝ ∞ χ := genericScaledCutoff_contDiff E _
    have hcχ : HasCompactSupport χ := genericScaledCutoff_compact E (by positivity)
    have hi0 := h0.locallyIntegrable.integrable_smul_left_of_hasCompactSupport
      ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const) (hcχ.fderiv_apply ℝ v)
    have hi1 := h1.locallyIntegrable.integrable_smul_left_of_hasCompactSupport hχ.continuous hcχ
    calc
      _ = ∫ x, (fderiv ℝ χ x v • (φ x*f x)) + χ x • (fderiv ℝ φ x v*f x) := by
        apply integral_congr_ae
        filter_upwards [] with x
        have hφ : ContDiff ℝ ∞ (fun z => φ z) := φ.smooth'
        change fderiv ℝ (fun z => χ z • φ z) x v * f x = _
        rw [cutoff_directional_product hχ hφ x v]
        simp only [Complex.real_smul]
        ring
      _ = _ := integral_add hi0 hi1
  have ht := ht0.add ht1
  simpa only [← he, zero_add] using ht

#print axioms generic_schwartz_cutoff_first_pairing_limit
end TheoremT.Continuum
