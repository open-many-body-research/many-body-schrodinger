import PhysicalSpectatorCutoffTransport_v1
import SpectatorIterationGeometry_v1

/-! Scheduled geometry may be pulled back into the actual N=2 spectator
coordinates without changing any of M,A,B,D,Q. All regions are exact preimages
and all differential cutoff expressions have been transported, not assumed. -/
noncomputable section
open scoped ContDiff
namespace TheoremT.Continuum.WeakGrushin

theorem SpectatorStepGeometry.pullback_physicalSpectatorReindex
    {c : ℝ} {Ω O W : Set (Space (Fin 3))} {χ η : Space (Fin 3) → ℝ}
    {M A B D Q : ℝ} (h : SpectatorStepGeometry c Ω O W χ η M A B D Q) :
    SpectatorStepGeometry c (physicalSpectatorReindex ⁻¹' Ω)
      (physicalSpectatorReindex ⁻¹' O) (physicalSpectatorReindex ⁻¹' W)
      (χ ∘ physicalSpectatorReindex) (η ∘ physicalSpectatorReindex) M A B D Q := by
  obtain ⟨hΩ,hχ,hcχ,hη,hcη,hηΩ,hW,hχW,hη1,hB,hD,hQ,hM,hA,hBχ,hDη,hQη,hχ1⟩ := h
  obtain ⟨hχe,hcχe,hsχe⟩ := physicalSpectatorReindex_cutoff_test hχ hcχ
  obtain ⟨hηe,hcηe,hsηe⟩ := physicalSpectatorReindex_cutoff_test hη hcη
  refine ⟨hΩ.preimage physicalSpectatorReindex.continuous,hχe,hcχe,hηe,hcηe,?_,
    hW.preimage physicalSpectatorReindex.continuous,?_,?_,hB,hD,hQ,?_,?_,?_,?_,?_,?_⟩
  · rw [hsηe]
    exact Set.preimage_mono hηΩ
  · rw [hsχe]
    exact Set.preimage_mono hχW
  · intro p hp
    exact hη1 (physicalSpectatorReindex p) hp
  · intro p
    exact hM (physicalSpectatorReindex p)
  · intro p hp
    rw [physicalSpectatorReindex_combinedCutoffScalar c hχ p]
    apply hA
    rwa [hsχe] at hp
  · intro p hp
    rw [physicalSpectatorReindex_cutoffGradientWeight c hχ p]
    apply hBχ
    rwa [hsχe] at hp
  · intro p
    exact hDη (physicalSpectatorReindex p)
  · intro p
    rw [physicalSpectatorReindex_grushinCutoffWeight c hη p]
    exact hQη (physicalSpectatorReindex p)
  · intro p hp
    exact hχ1 (physicalSpectatorReindex p) hp

#print axioms SpectatorStepGeometry.pullback_physicalSpectatorReindex
end TheoremT.Continuum.WeakGrushin
