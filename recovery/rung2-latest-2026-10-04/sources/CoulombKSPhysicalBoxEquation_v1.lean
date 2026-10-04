import PhysicalSpectatorWeakEquationTransport_v1
import PhysicalSpectatorL2BudgetTransport_v1
import CoulombEpsilonKSDifference_v1
import KSCommonAnnulusPatchAll_v1

/-! The actual normalized Coulomb KS equations on the common seven-coordinate
physical box. The nuclear principal constant is 4 and the unscaled pair-center
constant is 1. Both the solution and the source are the unchanged physical
functions pulled back by the proved spectator isometry. The original continuum
Coulomb graph implies the equation; no differentiated equation is an input. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum
open WeakGrushin

theorem scalar_coulomb_nuclear_physical_box_equation (i : Fin 2) 
    {Z E ε : ℝ} (hε : 0 < ε) (t0 : Position) (ht0 : ‖t0‖ = 1)
    {f : SpatialL2 2} (hgraph : scalarHamiltonianGraph 2 Z f ((E : ℂ) • f))
    {g : Configuration 2 → ℂ} (hg : Continuous g)
    (hfg : (f : Configuration 2 → ℂ) =ᵐ[volume] g) :
    ContDiffOn ℝ ∞ (epsilonNuclearKSPotential i ε Z E ∘ (physicalSpectatorReindexAt i).symm)
      (rectangularOpenBox (0,t0) (1/64) (1/64)) ∧
    ContDiffOn ℝ ∞ ((fun p => nuclearKSPotential i Z (ε*E) p • (-g 0)) ∘
      (physicalSpectatorReindexAt i).symm)
      (rectangularOpenBox (0,t0) (1/64) (1/64)) ∧
    ProductLocallyL2On ((originScaledDifference g ε ∘ (nuclearKSLift i)) ∘
      (physicalSpectatorReindexAt i).symm)
      (rectangularOpenBox (0,t0) (1/64) (1/64)) ∧
    ∀ φ : Space (Fin 3) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ rectangularOpenBox (0,t0) (1/64) (1/64) →
      Integrable (fun p => splitGrushin 4 oscillatorBasis
        (epsilonNuclearKSPotential i ε Z E ∘ (physicalSpectatorReindexAt i).symm) φ p •
        ((originScaledDifference g ε ∘ (nuclearKSLift i)) ∘
          (physicalSpectatorReindexAt i).symm) p) volume ∧
      Integrable (fun p => φ p • ((fun q => nuclearKSPotential i Z (ε*E) q • (-g 0)) ∘
        (physicalSpectatorReindexAt i).symm) p) volume ∧
      (∫ p, splitGrushin 4 oscillatorBasis
        (epsilonNuclearKSPotential i ε Z E ∘ (physicalSpectatorReindexAt i).symm) φ p •
        ((originScaledDifference g ε ∘ (nuclearKSLift i)) ∘
          (physicalSpectatorReindexAt i).symm) p) =
      ∫ p, φ p • ((fun q => nuclearKSPotential i Z (ε*E) q • (-g 0)) ∘
        (physicalSpectatorReindexAt i).symm) p := by
  have hPatch : physicalSpectatorReindexAt i ⁻¹'
      rectangularOpenBox (0,t0) (1/64) (1/64) ⊆ nuclearKSCoefficientPatch i := by
    exact physical_initialization_box_nuclear_patchAt i ht0
  have hPoint (p : Space (Fin 3)) (hp : p ∈ rectangularOpenBox (0,t0) (1/64) (1/64)) :
      (physicalSpectatorReindexAt i).symm p ∈ nuclearKSCoefficientPatch i := by
    apply hPatch
    simpa only [Set.mem_preimage,LinearIsometryEquiv.apply_symm_apply] using hp
  refine ⟨?_,?_,?_,?_⟩
  · intro p hp
    exact ((epsilonNuclearKSPotential_contDiffAt i ε Z E (hPoint p hp)).comp p
      (physicalSpectatorReindexAt_symm_contDiff i).contDiffAt).contDiffWithinAt
  · intro p hp
    exact (((nuclearKSPotential_contDiffAt i Z (ε*E) (hPoint p hp)).smul
      (contDiffAt_const (c := -g 0))).comp p
      (physicalSpectatorReindexAt_symm_contDiff i).contDiffAt).contDiffWithinAt
  · apply physicalSpectatorReindexAt_locallyL2 i
    exact product_continuousOn_locallyL2
      (((originScaledDifference_continuous hg ε).comp (nuclearKSLift_contDiff i).continuous).continuousOn)
  · apply physicalSpectatorReindexAt_weak_equation i 4
      (epsilonNuclearKSPotential i ε Z E) (originScaledDifference g ε ∘ nuclearKSLift i)
      (fun p => nuclearKSPotential i Z (ε*E) p • (-g 0))
    intro φ hφ hc hs
    have h := scalar_coulomb_epsilon_nuclear_KS_difference_weak i hε hgraph hg hfg hφ hc (hs.trans hPatch)
    simpa only [Function.comp_apply,Complex.real_smul,smul_neg,mul_neg] using h

theorem scalar_coulomb_pair_physical_box_equation 
    {Z E ε : ℝ} (hε : 0 < ε) (t0 : Position) (ht0 : ‖t0‖ = 1)
    {f : SpatialL2 2} (hgraph : scalarHamiltonianGraph 2 Z f ((E : ℂ) • f))
    {g : Configuration 2 → ℂ} (hg : Continuous g)
    (hfg : (f : Configuration 2 → ℂ) =ᵐ[volume] g) :
    ContDiffOn ℝ ∞ (epsilonPairKSPotential ε Z E ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm)
      (rectangularOpenBox (0,t0) (1/64) (1/64)) ∧
    ContDiffOn ℝ ∞ ((fun p => pairKSPotential Z (ε*E) p • (-g 0)) ∘
      (physicalSpectatorReindexAt (0 : Fin 2)).symm)
      (rectangularOpenBox (0,t0) (1/64) (1/64)) ∧
    ProductLocallyL2On ((originScaledDifference g ε ∘ pairKSLift) ∘
      (physicalSpectatorReindexAt (0 : Fin 2)).symm)
      (rectangularOpenBox (0,t0) (1/64) (1/64)) ∧
    ∀ φ : Space (Fin 3) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ rectangularOpenBox (0,t0) (1/64) (1/64) →
      Integrable (fun p => splitGrushin 1 oscillatorBasis
        (epsilonPairKSPotential ε Z E ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm) φ p •
        ((originScaledDifference g ε ∘ pairKSLift) ∘
          (physicalSpectatorReindexAt (0 : Fin 2)).symm) p) volume ∧
      Integrable (fun p => φ p • ((fun q => pairKSPotential Z (ε*E) q • (-g 0)) ∘
        (physicalSpectatorReindexAt (0 : Fin 2)).symm) p) volume ∧
      (∫ p, splitGrushin 1 oscillatorBasis
        (epsilonPairKSPotential ε Z E ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm) φ p •
        ((originScaledDifference g ε ∘ pairKSLift) ∘
          (physicalSpectatorReindexAt (0 : Fin 2)).symm) p) =
      ∫ p, φ p • ((fun q => pairKSPotential Z (ε*E) q • (-g 0)) ∘
        (physicalSpectatorReindexAt (0 : Fin 2)).symm) p := by
  have hPatch : physicalSpectatorReindexAt (0 : Fin 2) ⁻¹'
      rectangularOpenBox (0,t0) (1/64) (1/64) ⊆ pairKSCoefficientPatch := by
    exact (physical_initialization_box_subset_commonAnnulusAt (0 : Fin 2) ht0).trans
      ksCommonAnnulusRegion_subset_pair_patch
  have hPoint (p : Space (Fin 3)) (hp : p ∈ rectangularOpenBox (0,t0) (1/64) (1/64)) :
      (physicalSpectatorReindexAt (0 : Fin 2)).symm p ∈ pairKSCoefficientPatch := by
    apply hPatch
    simpa only [Set.mem_preimage,LinearIsometryEquiv.apply_symm_apply] using hp
  refine ⟨?_,?_,?_,?_⟩
  · intro p hp
    exact ((epsilonPairKSPotential_contDiffAt ε Z E (hPoint p hp)).comp p
      (physicalSpectatorReindexAt_symm_contDiff (0 : Fin 2)).contDiffAt).contDiffWithinAt
  · intro p hp
    exact (((pairKSPotential_contDiffAt Z (ε*E) (hPoint p hp)).smul
      (contDiffAt_const (c := -g 0))).comp p
      (physicalSpectatorReindexAt_symm_contDiff (0 : Fin 2)).contDiffAt).contDiffWithinAt
  · apply physicalSpectatorReindexAt_locallyL2 (0 : Fin 2)
    exact product_continuousOn_locallyL2
      (((originScaledDifference_continuous hg ε).comp pairKSLift_contDiff.continuous).continuousOn)
  · apply physicalSpectatorReindexAt_weak_equation (0 : Fin 2) 1
      (epsilonPairKSPotential ε Z E) (originScaledDifference g ε ∘ pairKSLift)
      (fun p => pairKSPotential Z (ε*E) p • (-g 0))
    intro φ hφ hc hs
    have h := scalar_coulomb_epsilon_pair_KS_difference_weak hε hgraph hg hfg hφ hc (hs.trans hPatch)
    simpa only [Function.comp_apply,Complex.real_smul,smul_neg,mul_neg] using h

end TheoremT.Continuum
