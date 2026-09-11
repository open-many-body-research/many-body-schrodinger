import ContinuumFoundation_v1
import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-! Full nonradial Bochner polar integration for actual additive Haar measure.
The angular measure is exactly Measure.toSphere, and the radial factor is the
actual finrank-minus-one Jacobian. Fubini conclusions require integrability.
No regularity, radiality, or angular spectral assertion is assumed. -/
noncomputable section
open MeasureTheory Set Function
open scoped ENNReal
namespace TheoremT.Polar

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (μ : Measure E) [μ.IsAddHaarMeasure]

theorem integrable_polar_product_iff (f : E → F) :
    Integrable f μ ↔ Integrable
      (fun p : Metric.sphere (0 : E) 1 × Ioi (0 : ℝ) => f (p.2.val • p.1.val))
      (μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
  have h := μ.measurePreserving_homeomorphUnitSphereProd.integrable_comp_emb
    (g := f ∘ Subtype.val ∘ (homeomorphUnitSphereProd E).symm)
    (Homeomorph.measurableEmbedding _)
  simp only [Function.comp_def, Homeomorph.symm_apply_apply] at h
  simp only [homeomorphUnitSphereProd_symm_apply_coe] at h
  have hs : IntegrableOn f ({(0 : E)}ᶜ) μ ↔
      Integrable (f ∘ Subtype.val) (μ.comap (Subtype.val : ({(0 : E)}ᶜ : Set E) → E)) :=
    integrableOn_iff_comap_subtypeVal (by measurability)
  rw [IntegrableOn, restrict_compl_singleton] at hs
  exact hs.trans h

theorem integral_polar_product (f : E → F) :
    (∫ x, f x ∂μ) = ∫ p : Metric.sphere (0 : E) 1 × Ioi (0 : ℝ),
      f (p.2.val • p.1.val)
      ∂(μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
  calc
    (∫ x, f x ∂μ) = ∫ x : ({(0)}ᶜ : Set E), f x.val ∂(μ.comap Subtype.val) := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl f,
        restrict_compl_singleton]
    _ = _ := by
      have h := μ.measurePreserving_homeomorphUnitSphereProd.integral_comp
        (Homeomorph.measurableEmbedding _)
        (f ∘ Subtype.val ∘ (homeomorphUnitSphereProd E).symm)
      simp only [Function.comp_apply, Homeomorph.symm_apply_apply] at h
      simpa only [Function.comp_def, homeomorphUnitSphereProd_symm_apply_coe] using h

theorem integral_volumeIoiPow (n : ℕ) (f : ℝ → F) :
    (∫ r : Ioi (0 : ℝ), f r.val ∂Measure.volumeIoiPow n) =
      ∫ r : ℝ in Ioi 0, r ^ n • f r := by
  simp only [Measure.volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul,
    integral_subtype_comap measurableSet_Ioi (fun r : ℝ => Real.toNNReal (r ^ n) • f r)]
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    change Real.toNNReal (r ^ n) • f r = r ^ n • f r
    rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg hr.out.le _)]
  · exact (measurable_subtype_coe.pow_const _).real_toNNReal

theorem integral_polar_sphere_outer (f : E → F) (hf : Integrable f μ) :
    (∫ x, f x ∂μ) = ∫ ω : Metric.sphere (0 : E) 1,
      (∫ r : ℝ in Ioi 0, r ^ (Module.finrank ℝ E - 1) • f (r • ω.val)) ∂μ.toSphere := by
  rw [integral_polar_product μ f, integral_prod _ ((integrable_polar_product_iff μ f).mp hf)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun ω => integral_volumeIoiPow _ (fun r => f (r • ω.val)))

theorem integral_polar_radius_outer (f : E → F) (hf : Integrable f μ) :
    (∫ x, f x ∂μ) = ∫ r : ℝ in Ioi 0,
      r ^ (Module.finrank ℝ E - 1) •
        (∫ ω : Metric.sphere (0 : E) 1, f (r • ω.val) ∂μ.toSphere) := by
  rw [integral_polar_product μ f,
    integral_prod_symm _ ((integrable_polar_product_iff μ f).mp hf)]
  exact integral_volumeIoiPow _ (fun r => ∫ ω : Metric.sphere (0 : E) 1,
    f (r • ω.val) ∂μ.toSphere)

#print axioms integrable_polar_product_iff
#print axioms integral_polar_product
#print axioms integral_volumeIoiPow
#print axioms integral_polar_sphere_outer
#print axioms integral_polar_radius_outer
end TheoremT.Polar
