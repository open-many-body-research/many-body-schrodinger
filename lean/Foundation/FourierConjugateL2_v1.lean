import ContinuumFoundation_v1
import Mathlib.Analysis.Fourier.LpSpace

/-! Unitary Fourier conjugation of actual bounded L2 operators. -/

noncomputable section
open MeasureTheory FourierTransform

namespace TheoremT.Continuum

def fourierConjugateL2 {N : ℕ}
    (M : SpatialL2 N →L[ℂ] SpatialL2 N) : SpatialL2 N →L[ℂ] SpatialL2 N :=
  fourierInvCLM ℂ (SpatialL2 N) ∘L M ∘L fourierCLM ℂ (SpatialL2 N)

theorem fourierConjugateL2_apply {N : ℕ}
    (M : SpatialL2 N →L[ℂ] SpatialL2 N) (f : SpatialL2 N) :
    fourierConjugateL2 M f = 𝓕⁻ (M (𝓕 f)) := rfl

theorem fourier_fourierConjugateL2 {N : ℕ}
    (M : SpatialL2 N →L[ℂ] SpatialL2 N) (f : SpatialL2 N) :
    𝓕 (fourierConjugateL2 M f) = M (𝓕 f) := by
  simp only [fourierConjugateL2_apply, fourier_fourierInv_eq]

theorem norm_fourierConjugateL2_apply {N : ℕ}
    (M : SpatialL2 N →L[ℂ] SpatialL2 N) (f : SpatialL2 N) :
    ‖fourierConjugateL2 M f‖ ≤ ‖M‖ * ‖f‖ := by
  rw [← Lp.norm_fourier_eq, fourier_fourierConjugateL2]
  simpa only [Lp.norm_fourier_eq] using M.le_opNorm (𝓕 f)

theorem norm_fourierConjugateL2_le {N : ℕ}
    (M : SpatialL2 N →L[ℂ] SpatialL2 N) :
    ‖fourierConjugateL2 M‖ ≤ ‖M‖ :=
  (fourierConjugateL2 M).opNorm_le_bound (norm_nonneg M)
    (norm_fourierConjugateL2_apply M)

#print axioms fourier_fourierConjugateL2
#print axioms norm_fourierConjugateL2_apply
#print axioms norm_fourierConjugateL2_le

end TheoremT.Continuum
