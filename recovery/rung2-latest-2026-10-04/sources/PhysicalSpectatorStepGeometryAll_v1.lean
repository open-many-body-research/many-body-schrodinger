import PhysicalSpectatorCutoffTransportAll_v1
import PhysicalSpectatorH12Geometry_v1

/-! Exact spectator-step geometry in either actual selected-electron space.
This adds the missing i=1 branch without changing the sealed i=0 construction. -/
noncomputable section
open scoped ContDiff
namespace TheoremT.Continuum.WeakGrushin

theorem SpectatorStepGeometry.pullback_physicalSpectatorReindexAt (i : Fin 2)
    {c : ℝ} {Ω O W : Set (Space (Fin 3))} {χ η : Space (Fin 3) → ℝ}
    {M A B D Q : ℝ} (h : SpectatorStepGeometry c Ω O W χ η M A B D Q) :
    SpectatorStepGeometry c (physicalSpectatorReindexAt i ⁻¹' Ω)
      (physicalSpectatorReindexAt i ⁻¹' O) (physicalSpectatorReindexAt i ⁻¹' W)
      (χ ∘ physicalSpectatorReindexAt i) (η ∘ physicalSpectatorReindexAt i) M A B D Q := by
  obtain ⟨hΩ,hχ,hcχ,hη,hcη,hηΩ,hW,hχW,hη1,hB,hD,hQ,hM,hA,hBχ,hDη,hQη,hχ1⟩ := h
  obtain ⟨hχe,hcχe,hsχe⟩ := physicalSpectatorReindexAt_cutoff_test i hχ hcχ
  obtain ⟨hηe,hcηe,hsηe⟩ := physicalSpectatorReindexAt_cutoff_test i hη hcη
  refine ⟨hΩ.preimage (physicalSpectatorReindexAt i).continuous,hχe,hcχe,hηe,hcηe,?_,
    hW.preimage (physicalSpectatorReindexAt i).continuous,?_,?_,hB,hD,hQ,?_,?_,?_,?_,?_,?_⟩
  · rw [hsηe]
    exact Set.preimage_mono hηΩ
  · rw [hsχe]
    exact Set.preimage_mono hχW
  · intro p hp
    exact hη1 (physicalSpectatorReindexAt i p) hp
  · intro p
    exact hM (physicalSpectatorReindexAt i p)
  · intro p hp
    rw [physicalSpectatorReindexAt_combinedCutoffScalar i c hχ p]
    apply hA
    rwa [hsχe] at hp
  · intro p hp
    rw [physicalSpectatorReindexAt_cutoffGradientWeight i c hχ p]
    apply hBχ
    rwa [hsχe] at hp
  · intro p
    exact hDη (physicalSpectatorReindexAt i p)
  · intro p
    rw [physicalSpectatorReindexAt_grushinCutoffWeight i c hη p]
    exact hQη (physicalSpectatorReindexAt i p)
  · intro p hp
    exact hχ1 (physicalSpectatorReindexAt i p) hp

theorem physical_h12_spectatorStepGeometryAt (i : Fin 2) (a : Space (Fin 3))
    {c C1 C2 ry rt δ S : ℝ}
    (hc : 0 ≤ c) (hδ : 0 < δ) (hy : 2*δ ≤ ry) (ht : 2*δ ≤ rt)
    (hC1 : ∀ x, |deriv Real.smoothTransition x| ≤ C1)
    (hC2 : ∀ x, |deriv (deriv Real.smoothTransition) x| ≤ C2)
    (hS : ‖a.1‖+2*ry ≤ S) :
    SpectatorStepGeometry c
      (physicalSpectatorReindexAt i ⁻¹' rectangularOpenBox a ry rt)
      (physicalSpectatorReindexAt i ⁻¹' rectangularOpenBox a (ry-2*δ) (rt-2*δ))
      (physicalSpectatorReindexAt i ⁻¹' rectangularOpenBox a (ry-δ) (rt-δ))
      (h12InnerCutoff a ry rt δ ∘ physicalSpectatorReindexAt i)
      (h12EnergyCutoff a ry rt δ ∘ physicalSpectatorReindexAt i)
      1 (h12CutoffScalarBound c S C1 C2 δ) (h12CutoffWeightBound c S C1 δ)
      1 (h12CutoffWeightBound c S C1 δ) :=
  (h12_spectatorStepGeometry a hc hδ hy ht hC1 hC2 hS).pullback_physicalSpectatorReindexAt i

#print axioms SpectatorStepGeometry.pullback_physicalSpectatorReindexAt
#print axioms physical_h12_spectatorStepGeometryAt
end TheoremT.Continuum.WeakGrushin
