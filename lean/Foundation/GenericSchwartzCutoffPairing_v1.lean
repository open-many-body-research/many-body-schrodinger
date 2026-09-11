import GenericCutoffIntegralLimits_v1
import GenericWeakEllipticGain_v1
import SecondDirectionalSmul_v1

set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Filter TemperedDistribution
open scoped SchwartzMap Laplacian LineDeriv ContDiff Topology
namespace TheoremT.Continuum
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem generic_compact_lp_product_integrable (f : Lp ℂ 2 (volume : Measure E))
    {φ : E → ℂ} (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    Integrable (fun x => φ x * f x) volume := by
  simpa only [smul_eq_mul] using
    ((Lp.memLp f).locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport hφ hc

theorem generic_schwartz_lp_product_integrable (φ : 𝓢(E,ℂ)) (f : Lp ℂ 2 (volume : Measure E)) :
    Integrable (fun x => φ x * f x) volume := by
  simpa only [Pi.mul_def] using
    (memLp_one_iff_integrable.mp ((Lp.memLp f).mul (r := 1) (φ.memLp 2 (volume : Measure E))))

theorem generic_schwartz_cutoff_pairing_limit (φ : 𝓢(E,ℂ)) (f : Lp ℂ 2 (volume : Measure E)) :
    Tendsto (fun n : ℕ => ∫ x, (genericScaledCutoff E ((n : ℝ)+1) x • φ x) * f x)
      atTop (𝓝 (∫ x, φ x * f x)) := by
  simpa only [smul_mul_assoc] using generic_cutoff_integral_limit (generic_schwartz_lp_product_integrable φ f)

theorem generic_schwartz_cutoff_second_pairing_limit
    (φ : 𝓢(E,ℂ)) (f : Lp ℂ 2 (volume : Measure E)) (v : E) :
    Tendsto (fun n : ℕ => ∫ x,
      fderiv ℝ (fun y => fderiv ℝ (fun z => genericScaledCutoff E ((n : ℝ)+1) z • φ z) y v) x v * f x)
      atTop (𝓝 (∫ x, fderiv ℝ (fun y => fderiv ℝ φ y v) x v * f x)) := by
  have hD : ((∂_{v} φ : 𝓢(E,ℂ)) : E → ℂ) = (fun y => fderiv ℝ φ y v) := by
    funext y; exact SchwartzMap.lineDerivOp_apply_eq_fderiv v φ y
  have h0 := generic_schwartz_lp_product_integrable φ f
  have h1 : Integrable (fun x => fderiv ℝ φ x v * f x) volume := by
    simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv] using generic_schwartz_lp_product_integrable (∂_{v} φ) f
  have h2 : Integrable (fun x => fderiv ℝ (fun y => fderiv ℝ φ y v) x v * f x) volume := by
    simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv, hD] using generic_schwartz_lp_product_integrable (∂_{v} (∂_{v} φ)) f
  have ht0 := generic_cutoff_second_integral_limit h0 v v
  have ht1 := generic_cutoff_first_integral_limit h1 v
  have ht2 := generic_cutoff_integral_limit h2
  have he (n : ℕ) :
      (∫ x, fderiv ℝ (fun y => fderiv ℝ (fun z => genericScaledCutoff E ((n : ℝ)+1) z • φ z) y v) x v * f x) =
      (∫ x, fderiv ℝ (fun y => fderiv ℝ (genericScaledCutoff E ((n : ℝ)+1)) y v) x v • (φ x*f x)) +
      (2 : ℂ)*(∫ x, fderiv ℝ (genericScaledCutoff E ((n : ℝ)+1)) x v • (fderiv ℝ φ x v*f x)) +
      (∫ x, genericScaledCutoff E ((n : ℝ)+1) x • (fderiv ℝ (fun y => fderiv ℝ φ y v) x v*f x)) := by
    let χ := genericScaledCutoff E ((n : ℝ)+1)
    have hχ : ContDiff ℝ ∞ χ := genericScaledCutoff_contDiff E _
    have hcχ : HasCompactSupport χ := genericScaledCutoff_compact E (by positivity)
    have hχd : ContDiff ℝ ∞ (fun y => fderiv ℝ χ y v) :=
      (hχ.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
    have hi0 := h0.locallyIntegrable.integrable_smul_left_of_hasCompactSupport
      ((hχd.continuous_fderiv (by simp)).clm_apply continuous_const)
      ((hcχ.fderiv_apply ℝ v).fderiv_apply ℝ v)
    have hi1 := h1.locallyIntegrable.integrable_smul_left_of_hasCompactSupport
      hχd.continuous (hcχ.fderiv_apply ℝ v)
    have hi2 := h2.locallyIntegrable.integrable_smul_left_of_hasCompactSupport hχ.continuous hcχ
    calc
      _ = ∫ x, (fderiv ℝ (fun y => fderiv ℝ χ y v) x v • (φ x*f x)) +
          (2 : ℂ)*(fderiv ℝ χ x v • (fderiv ℝ φ x v*f x)) +
          χ x • (fderiv ℝ (fun y => fderiv ℝ φ y v) x v*f x) := by
        apply integral_congr_ae
        filter_upwards [] with x
        change fderiv ℝ (fun y => fderiv ℝ (fun z => χ z • φ z) y v) x v * f x = _
        have hφ : ContDiff ℝ ∞ (fun x => φ x) := φ.smooth'
        rw [second_same_directional_smul hχ hφ x v]
        simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat]
        ring
      _ = _ := by
        have hs0 := integral_add hi0 (hi1.const_mul (2 : ℂ))
        have hs := integral_add (hi0.add (hi1.const_mul (2 : ℂ))) hi2
        simp only [Pi.add_apply] at hs hs0
        rw [hs, hs0, integral_const_mul]
  have ht := (ht0.add (ht1.const_mul (2 : ℂ))).add ht2
  simpa only [← he, mul_zero, zero_add] using ht

#print axioms generic_schwartz_cutoff_second_pairing_limit
end TheoremT.Continuum
