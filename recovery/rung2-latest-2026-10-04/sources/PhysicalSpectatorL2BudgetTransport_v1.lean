import PhysicalSpectatorReindexAll_v1
import ProductCoordinateWeakHk_v1
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! Exact preservation of physical spectator L2 budgets under the proved
coordinate reindexing. The measures are the actual product volumes, and the
same squared-integral budget is retained without a dimension factor. -/
noncomputable section
open MeasureTheory Filter
namespace TheoremT.Continuum
open WeakGrushin

theorem physicalSpectatorReindexAt_symm_measurePreserving (i : Fin 2) :
    MeasurePreserving (physicalSpectatorReindexAt i).symm volume volume := by
  exact (MeasurePreserving.id (volume : Measure KSSpace)).prod
    (twoElectronSpectatorPositionEquiv i).symm.measurePreserving

theorem physicalSpectatorReindexAt_regionL2Budget (i : Fin 2)
    {O : Set (Space (Fin 3))} {f : NuclearKSSpace i → ℂ} {W : ℝ}
    (hf : RegionL2Budget f (physicalSpectatorReindexAt i ⁻¹' O) W) :
    RegionL2Budget (f ∘ (physicalSpectatorReindexAt i).symm) O W := by
  have himg : (physicalSpectatorReindexAt i).symm '' O = physicalSpectatorReindexAt i ⁻¹' O := by
    ext p
    constructor
    · rintro ⟨q,hq,rfl⟩
      simpa only [Set.mem_preimage,LinearIsometryEquiv.apply_symm_apply] using hq
    · intro hp
      exact ⟨physicalSpectatorReindexAt i p,hp,(physicalSpectatorReindexAt i).symm_apply_apply p⟩
  have hm := (physicalSpectatorReindexAt_symm_measurePreserving i).restrict_image_emb
    (physicalSpectatorReindexAt i).symm.toHomeomorph.measurableEmbedding O
  rw [himg] at hm
  refine ⟨hf.1.comp_measurePreserving hm,?_⟩
  exact (hm.integral_comp (physicalSpectatorReindexAt i).symm.toHomeomorph.measurableEmbedding
    (fun p => ‖f p‖^2)).trans_le hf.2

theorem physicalSpectatorReindexAt_locallyL2 (i : Fin 2)
    {O : Set (Space (Fin 3))} {f : NuclearKSSpace i → ℂ}
    (hf : ProductLocallyL2On f (physicalSpectatorReindexAt i ⁻¹' O)) :
    ProductLocallyL2On (f ∘ (physicalSpectatorReindexAt i).symm) O := by
  intro K hK hKO
  have himage : IsCompact ((physicalSpectatorReindexAt i).symm '' K) :=
    hK.image (physicalSpectatorReindexAt i).symm.continuous
  have hs : (physicalSpectatorReindexAt i).symm '' K ⊆ physicalSpectatorReindexAt i ⁻¹' O := by
    rintro p ⟨q,hq,rfl⟩
    simpa only [Set.mem_preimage,LinearIsometryEquiv.apply_symm_apply] using hKO hq
  exact (hf _ himage hs).comp_measurePreserving
    ((physicalSpectatorReindexAt_symm_measurePreserving i).restrict_image_emb
      (physicalSpectatorReindexAt i).symm.toHomeomorph.measurableEmbedding K)

end TheoremT.Continuum
