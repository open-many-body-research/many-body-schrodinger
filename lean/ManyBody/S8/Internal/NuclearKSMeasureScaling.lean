import ManyBody.S8.Internal.NuclearKSAnisotropicScaling
import NuclearKSVolumeHaar_v1
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! Actual product Lebesgue transport under positive nuclear KS dilation.
A positive finite Haar scalar is proved from the explicit linear equivalence;
no supplied pushforward or false product isometry is used.
-/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
open TheoremT.Continuum

namespace ManyBody.S8

def nuclearKSAnisotropicEquiv {N : ℕ} (i : Fin N) {r : ℝ} (hr : 0 < r) :
    NuclearKSSpace i ≃L[ℝ] NuclearKSSpace i :=
  ((LinearEquiv.smulOfNeZero ℝ KSSpace (Real.sqrt r) (Real.sqrt_pos.mpr hr).ne').prodCongr
    (LinearEquiv.smulOfNeZero ℝ (SpectatorConfiguration i) r hr.ne')).toContinuousLinearEquiv

theorem nuclearKSAnisotropicEquiv_apply {N : ℕ} (i : Fin N) {r : ℝ}
    (hr : 0 < r) (q : NuclearKSSpace i) :
    nuclearKSAnisotropicEquiv i hr q = nuclearKSAnisotropicScale i r q := by
  rfl

theorem nuclearKSAnisotropicEquiv_clm {N : ℕ} (i : Fin N) {r : ℝ} (hr : 0 < r) :
    (nuclearKSAnisotropicEquiv i hr).toContinuousLinearMap = nuclearKSAnisotropicScaleCLM i r := by
  apply ContinuousLinearMap.ext
  intro q
  exact (nuclearKSAnisotropicEquiv_apply i hr q).trans
    (nuclearKSAnisotropicScaleCLM_apply i r q).symm

theorem nuclearKSAnisotropicEquiv_map_volume {N : ℕ} (i : Fin N) {r : ℝ}
    (hr : 0 < r) :
    ∃ J : ℝ≥0, 0 < J ∧
      (volume : Measure (NuclearKSSpace i)).map (nuclearKSAnisotropicEquiv i hr) =
        (J : ℝ≥0∞) • volume := by
  have := nuclearKS_volume_isAddHaar i
  let e := nuclearKSAnisotropicEquiv i hr
  have : ((volume : Measure (NuclearKSSpace i)).map e).IsAddHaarMeasure :=
    e.isAddHaarMeasure_map volume
  exact ⟨Measure.addHaarScalarFactor (volume.map e) volume,
    Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (volume.map e) volume,
    Measure.isAddLeftInvariant_eq_smul (volume.map e) volume⟩

theorem nuclearKSAnisotropicEquiv_integral_transport {N : ℕ} (i : Fin N) {r : ℝ}
    (hr : 0 < r) :
    ∃ J : ℝ, 0 < J ∧ ∀ F : NuclearKSSpace i → ℂ,
      (Integrable F volume ↔ Integrable (F ∘ nuclearKSAnisotropicEquiv i hr) volume) ∧
      (∫ q, F (nuclearKSAnisotropicEquiv i hr q)) = J • (∫ p, F p) := by
  obtain ⟨J, hJpos, hJ⟩ := nuclearKSAnisotropicEquiv_map_volume i hr
  refine ⟨J, by exact_mod_cast hJpos, ?_⟩
  intro F
  have hJne : (J : ℝ≥0∞) ≠ 0 := by exact_mod_cast hJpos.ne'
  have he : MeasurableEmbedding (nuclearKSAnisotropicEquiv i hr) :=
    (nuclearKSAnisotropicEquiv i hr).toHomeomorph.measurableEmbedding
  constructor
  · have hi : Integrable F (volume.map (nuclearKSAnisotropicEquiv i hr)) ↔
        Integrable (F ∘ nuclearKSAnisotropicEquiv i hr) volume := he.integrable_map_iff
    rw [hJ, integrable_smul_measure hJne ENNReal.coe_ne_top] at hi
    exact hi
  · have hi := he.integral_map (μ := volume) F
    rw [hJ, integral_smul_measure] at hi
    simpa only [ENNReal.coe_toReal] using hi.symm

#print axioms nuclearKSAnisotropicEquiv_map_volume
#print axioms nuclearKSAnisotropicEquiv_integral_transport
end ManyBody.S8
