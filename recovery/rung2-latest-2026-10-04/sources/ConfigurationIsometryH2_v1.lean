import FourierConfigurationIsometry_v1

/-! Orthogonal covariance on the unchanged weak H² domain and its actual
distributional Laplacian. No potential invariance is needed here. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped SchwartzMap Laplacian
namespace TheoremT.Continuum

theorem HasH2.configurationIsometryPull {N : ℕ} {f : SpatialL2 N}
    (hf : HasH2 f) (U : Configuration N ≃ₗᵢ[ℝ] Configuration N) :
    HasH2 (configurationIsometryPull U f) := by
  apply (hasH2_iff_fourier_normSq_memLp _).mpr
  have h := configurationIsometryPull_fourier_weight U f
    (by simpa only [Complex.ofReal_pow] using
      (hasH2_iff_fourier_normSq_memLp f).mp hf)
  simpa only [Complex.ofReal_pow] using h

theorem configurationIsometryPull_laplacian {N : ℕ}
    (U : Configuration N ≃ₗᵢ[ℝ] Configuration N) (f w : SpatialL2 N)
    (h : Δ (f : 𝓢'(Configuration N, ℂ)) = (w : 𝓢'(Configuration N, ℂ))) :
    Δ (configurationIsometryPull U f : 𝓢'(Configuration N, ℂ)) =
      (configurationIsometryPull U w : 𝓢'(Configuration N, ℂ)) := by
  have hf := (hasH2_iff_exists_temperedDistribution_laplacian f).mpr ⟨w,h⟩
  obtain ⟨v,hv⟩ := (hf.configurationIsometryPull U).exists_temperedDistribution_laplacian
  have heq : v = configurationIsometryPull U w := by
    apply (Lp.fourierTransformₗᵢ (Configuration N) ℂ).injective
    change 𝓕 v = 𝓕 (configurationIsometryPull U w)
    rw [fourier_configurationIsometryPull]
    apply Lp.ext
    have ht := U.measurePreserving.quasiMeasurePreserving.ae (fourier_laplacian_ae f w h)
    have hfU := configurationIsometryPull_ae U (𝓕 f)
    rw [← fourier_configurationIsometryPull] at hfU
    filter_upwards [fourier_laplacian_ae (configurationIsometryPull U f) v hv,
      configurationIsometryPull_ae U (𝓕 w), hfU, ht] with x hx hwx hfx htx
    simp only [Function.comp_apply,U.norm_map] at *
    rw [hx,hwx,hfx,htx]
  simpa only [heq] using hv

#print axioms HasH2.configurationIsometryPull
#print axioms configurationIsometryPull_laplacian
end TheoremT.Continuum
