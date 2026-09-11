import ComplexSphereCalculus_v1

/-! The sharp sphere Poincare inequality for actual complex C1 functions.
The sphere uses Euclidean area (mass 4*pi), not a probability convention. -/
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory
open scoped ContDiff BigOperators
namespace TheoremT.Polar
open TheoremT.HydrogenPolynomial TheoremT.HydrogenSphereC1Limit

theorem continuous_sphere_norm_sq_components
    {h : Metric.sphere (0 : AngularR3) 1 → ℂ} (hh : Continuous h) :
    (∫ w, ‖h w‖^2 ∂sphereMeasure) =
      (∫ w, (h w).re^2 ∂sphereMeasure) + (∫ w, (h w).im^2 ∂sphereMeasure) := by
  simp_rw [complex_norm_sq_components]
  apply integral_add
  · exact (Complex.continuous_re.comp hh).pow 2 |>.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact (Complex.continuous_im.comp hh).pow 2 |>.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

theorem complex_sphere_poincare {f : AngularR3 → ℂ} (hf : ContDiff ℝ 1 f) :
    2 * (∫ w : Metric.sphere (0 : AngularR3) 1,
      ‖f w.val - normalizedSphereMean (fun v => f v.val)‖^2 ∂sphereMeasure) ≤
      ∑ i : Fin 3, ∫ w : Metric.sphere (0 : AngularR3) 1,
        ‖complexTangentialPartial i f w.val‖^2 ∂sphereMeasure := by
  have hfr : ContDiff ℝ 1 (fun x => (f x).re) := Complex.reCLM.contDiff.comp hf
  have hfi : ContDiff ℝ 1 (fun x => (f x).im) := Complex.imCLM.contDiff.comp hf
  have hd : Differentiable ℝ f := hf.differentiable (by simp)
  have hre := sphere_poincare_contDiff_one hfr
  have him := sphere_poincare_contDiff_one hfi
  simp only [sphereAngularInner, sphereTangentialEnergy, ← pow_two,
    tangential_complex_re hd] at hre
  simp only [sphereAngularInner, sphereTangentialEnergy, ← pow_two,
    tangential_complex_im hd] at him
  have hl := continuous_sphere_norm_sq_components
    ((hf.continuous.comp continuous_subtype_val).sub continuous_const
      (g := fun _ => normalizedSphereMean (fun v => f v.val)))
  simp only [Pi.sub_apply, Function.comp_apply, Complex.sub_re, Complex.sub_im, normalizedSphereMean_re hf.continuous,
    normalizedSphereMean_im hf.continuous] at hl
  have hr : (∑ i : Fin 3, ∫ w : Metric.sphere (0 : AngularR3) 1,
        ‖complexTangentialPartial i f w.val‖^2 ∂sphereMeasure) =
      (∑ i : Fin 3, ∫ w : Metric.sphere (0 : AngularR3) 1,
        (complexTangentialPartial i f w.val).re^2 ∂sphereMeasure) +
      (∑ i : Fin 3, ∫ w : Metric.sphere (0 : AngularR3) 1,
        (complexTangentialPartial i f w.val).im^2 ∂sphereMeasure) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact continuous_sphere_norm_sq_components
      ((continuous_complexTangentialPartial hf i).comp continuous_subtype_val)
  rw [hl, hr, mul_add]
  exact add_le_add hre him

theorem complex_sphere_poincare_mean_zero {f : AngularR3 → ℂ}
    (hf : ContDiff ℝ 1 f)
    (hm : (∫ w : Metric.sphere (0 : AngularR3) 1, f w.val ∂sphereMeasure) = 0) :
    2 * (∫ w : Metric.sphere (0 : AngularR3) 1, ‖f w.val‖^2 ∂sphereMeasure) ≤
      ∑ i : Fin 3, ∫ w : Metric.sphere (0 : AngularR3) 1,
        ‖complexTangentialPartial i f w.val‖^2 ∂sphereMeasure := by
  have hz : normalizedSphereMean (fun w => f w.val) = 0 := by
    simp only [normalizedSphereMean, hm, smul_zero]
  simpa only [hz, sub_zero] using complex_sphere_poincare hf

#print axioms complex_sphere_poincare
#print axioms complex_sphere_poincare_mean_zero
end TheoremT.Polar
