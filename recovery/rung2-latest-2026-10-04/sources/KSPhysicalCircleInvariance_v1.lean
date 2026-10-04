import KSCircleContinuousLinear_v1
import PhysicalSpectatorReindexAll_v1
import NuclearKSLift_v1

/-! Exact circle invariance of both literal nuclear charts and the literal
pair chart, including the inverse physical spectator reindexing. These
identities apply to every scalar configuration function, so also to the
normalized origin differences used in the physical analytic estimates. -/
set_option autoImplicit false
noncomputable section
namespace TheoremT.Continuum

theorem nuclearKSLift_physical_circle_invariant (i : Fin 2)
    {a b : ℝ} (h : a^2+b^2=1) (q : WeakGrushin.Space (Fin 3)) :
    nuclearKSLift i ((physicalSpectatorReindexAt i).symm (ksCircleProductCLM a b q)) =
      nuclearKSLift i ((physicalSpectatorReindexAt i).symm q) := by
  simp only [physicalSpectatorReindexAt_symm_apply,ksCircleProductCLM_apply,
    nuclearKSLift,ksMap_circle_invariant h]

theorem pairKSLift_physical_circle_invariant
    {a b : ℝ} (h : a^2+b^2=1) (q : WeakGrushin.Space (Fin 3)) :
    pairKSLift ((physicalSpectatorReindexAt (0 : Fin 2)).symm (ksCircleProductCLM a b q)) =
      pairKSLift ((physicalSpectatorReindexAt (0 : Fin 2)).symm q) := by
  simp only [physicalSpectatorReindexAt_symm_apply,ksCircleProductCLM_apply,
    pairKSLift,ksMap_circle_invariant h]

theorem nuclearKSPhysicalPullback_circle_invariant (g : Configuration 2 → ℂ) (i : Fin 2)
    {a b : ℝ} (h : a^2+b^2=1) (q : WeakGrushin.Space (Fin 3)) :
    ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm)
        (ksCircleProductCLM a b q) =
      ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm) q := by
  simp only [Function.comp_apply,nuclearKSLift_physical_circle_invariant i h]

theorem pairKSPhysicalPullback_circle_invariant (g : Configuration 2 → ℂ)
    {a b : ℝ} (h : a^2+b^2=1) (q : WeakGrushin.Space (Fin 3)) :
    ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm)
        (ksCircleProductCLM a b q) =
      ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm) q := by
  simp only [Function.comp_apply,pairKSLift_physical_circle_invariant h]

end TheoremT.Continuum
