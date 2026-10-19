import PhysicalSpectatorStepGeometry_v1
import GrushinH12CutoffData_v1

/-! The existing two-gap H12 cutoff is an actual spectator-step geometry,
and its exact pullback supplies the same constants in physical coordinates. -/
noncomputable section
open scoped ContDiff
namespace TheoremT.Continuum.WeakGrushin

theorem h12_spectatorStepGeometry (a : Space (Fin 3)) {c C1 C2 ry rt δ S : ℝ}
    (hc : 0 ≤ c) (hδ : 0 < δ) (hy : 2*δ ≤ ry) (ht : 2*δ ≤ rt)
    (hC1 : ∀ x, |deriv Real.smoothTransition x| ≤ C1)
    (hC2 : ∀ x, |deriv (deriv Real.smoothTransition) x| ≤ C2)
    (hS : ‖a.1‖+2*ry ≤ S) :
    SpectatorStepGeometry c (rectangularOpenBox a ry rt)
      (rectangularOpenBox a (ry-2*δ) (rt-2*δ))
      (rectangularOpenBox a (ry-δ) (rt-δ))
      (h12InnerCutoff a ry rt δ) (h12EnergyCutoff a ry rt δ)
      1 (h12CutoffScalarBound c S C1 C2 δ) (h12CutoffWeightBound c S C1 δ)
      1 (h12CutoffWeightBound c S C1 δ) := by
  obtain ⟨hχ,hcχ,hη,hcη,hηΩ,hχW,hη1,hχ1⟩ := h12_cutoff_geometry a hδ hy ht
  obtain ⟨hM,hD⟩ := h12_cutoff_value_bounds a ry rt δ
  obtain ⟨hA,hB,hQ⟩ := h12_cutoff_coefficient_bounds a hc hδ hy ht hC1 hC2 hS
  have hn := h12CutoffWeightBound_nonneg hc S C1 δ
  refine ⟨rectangularOpenBox_isOpen a ry rt,hχ,hcχ,hη,hcη,hηΩ,
    rectangularOpenBox_isOpen a (ry-δ) (rt-δ),hχW,hη1,hn,zero_le_one,hn,
    hM,fun p _ => hA p,fun p _ => hB p,hD,hQ,?_⟩
  intro p hp
  exact hχ1 p (rectangularOpenBox_subset_closedBox a _ _ hp)

theorem physical_h12_spectatorStepGeometry (a : Space (Fin 3))
    {c C1 C2 ry rt δ S : ℝ}
    (hc : 0 ≤ c) (hδ : 0 < δ) (hy : 2*δ ≤ ry) (ht : 2*δ ≤ rt)
    (hC1 : ∀ x, |deriv Real.smoothTransition x| ≤ C1)
    (hC2 : ∀ x, |deriv (deriv Real.smoothTransition) x| ≤ C2)
    (hS : ‖a.1‖+2*ry ≤ S) :
    SpectatorStepGeometry c
      (physicalSpectatorReindex ⁻¹' rectangularOpenBox a ry rt)
      (physicalSpectatorReindex ⁻¹' rectangularOpenBox a (ry-2*δ) (rt-2*δ))
      (physicalSpectatorReindex ⁻¹' rectangularOpenBox a (ry-δ) (rt-δ))
      (h12InnerCutoff a ry rt δ ∘ physicalSpectatorReindex)
      (h12EnergyCutoff a ry rt δ ∘ physicalSpectatorReindex)
      1 (h12CutoffScalarBound c S C1 C2 δ) (h12CutoffWeightBound c S C1 δ)
      1 (h12CutoffWeightBound c S C1 δ) :=
  (h12_spectatorStepGeometry a hc hδ hy ht hC1 hC2 hS).pullback_physicalSpectatorReindex

#print axioms h12_spectatorStepGeometry
#print axioms physical_h12_spectatorStepGeometry
end TheoremT.Continuum.WeakGrushin
