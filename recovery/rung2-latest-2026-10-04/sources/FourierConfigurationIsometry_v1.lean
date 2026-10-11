import FourierSobolevDomain_v1
import WeakLaplacianDistribution_v1

/-! Orthogonal change of configuration coordinates on the actual L² Fourier
transform. This lemma is independent of invariance of a particular potential. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped SchwartzMap
namespace TheoremT.Continuum

def configurationIsometryPull {N : ℕ}
    (U : Configuration N ≃ₗᵢ[ℝ] Configuration N) : SpatialL2 N →ₗᵢ[ℂ] SpatialL2 N :=
  Lp.compMeasurePreservingₗᵢ ℂ U U.measurePreserving

theorem configurationIsometryPull_ae {N : ℕ}
    (U : Configuration N ≃ₗᵢ[ℝ] Configuration N) (f : SpatialL2 N) :
    configurationIsometryPull U f =ᵐ[volume] f ∘ U :=
  Lp.coeFn_compMeasurePreserving f U.measurePreserving

theorem configurationIsometryPull_schwartz {N : ℕ}
    (U : Configuration N ≃ₗᵢ[ℝ] Configuration N) (f : 𝓢(Configuration N,ℂ)) :
    configurationIsometryPull U (f.toLp 2 volume) =
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ U.toContinuousLinearEquiv f).toLp 2 volume := by
  apply Lp.ext
  have ha := configurationIsometryPull_ae U (f.toLp 2 volume)
  have hb := U.measurePreserving.quasiMeasurePreserving.ae (f.coeFn_toLp 2 volume)
  have hc := SchwartzMap.coeFn_toLp
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ U.toContinuousLinearEquiv f) 2 volume
  filter_upwards [ha,hb,hc] with x hx hy hz
  rw [hx,hz]
  exact hy

theorem fourier_configurationIsometryPull {N : ℕ}
    (U : Configuration N ≃ₗᵢ[ℝ] Configuration N) (f : SpatialL2 N) :
    𝓕 (configurationIsometryPull U f) = configurationIsometryPull U (𝓕 f) := by
  let p := fun f : SpatialL2 N =>
    𝓕 (configurationIsometryPull U f) = configurationIsometryPull U (𝓕 f)
  apply DenseRange.induction_on (p := p)
    (SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top) f
  · apply isClosed_eq
    · exact (fourierCLM ℂ (SpatialL2 N)).continuous.comp (configurationIsometryPull U).continuous
    · exact (configurationIsometryPull U).continuous.comp (fourierCLM ℂ (SpatialL2 N)).continuous
  intro u
  change 𝓕 (configurationIsometryPull U (u.toLp 2)) = configurationIsometryPull U (𝓕 (u.toLp 2))
  rw [configurationIsometryPull_schwartz,SchwartzMap.toLp_fourier_eq,
    SchwartzMap.toLp_fourier_eq,configurationIsometryPull_schwartz]
  congr 1
  ext x
  exact Real.fourier_comp_linearIsometry U u x

theorem configurationIsometryPull_fourier_weight {N : ℕ}
    (U : Configuration N ≃ₗᵢ[ℝ] Configuration N) (f : SpatialL2 N)
    (hf : MemLp (fun x : Configuration N => (‖x‖^2 : ℂ) * (𝓕 f) x) 2 volume) :
    MemLp (fun x : Configuration N => (‖x‖^2 : ℂ) * (𝓕 (configurationIsometryPull U f)) x) 2 volume := by
  have h := hf.comp_measurePreserving U.measurePreserving
  rw [fourier_configurationIsometryPull]
  apply h.ae_eq
  filter_upwards [configurationIsometryPull_ae U (𝓕 f)] with x hx
  simp only [Function.comp_apply,U.norm_map] at *
  rw [hx]

#print axioms fourier_configurationIsometryPull
#print axioms configurationIsometryPull_fourier_weight
end TheoremT.Continuum
