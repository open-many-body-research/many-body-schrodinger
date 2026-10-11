import PhysicalSpectatorCutoffTransportAll_v1
import GrushinHoleCommutator_v1
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! Exact original weak Grushin equation transport from either physical
spectator index type to Fin 3. The map preserves the actual product volume;
test derivatives are transported by its proved linear coordinate action. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators
namespace TheoremT.Continuum
open WeakGrushin

theorem physicalSpectatorReindexAt_measurePreserving (i : Fin 2) :
    MeasurePreserving (physicalSpectatorReindexAt i) volume volume := by
  exact (MeasurePreserving.id (volume : Measure KSSpace)).prod
    (twoElectronSpectatorPositionEquiv i).measurePreserving

theorem physicalSpectatorReindexAt_splitGrushin (i : Fin 2) (c : ℝ)
    (B : Space (Fin 3) → ℝ) {φ : Space (Fin 3) → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (p : NuclearKSSpace i) :
    splitGrushin c spectatorBasis (B ∘ physicalSpectatorReindexAt i)
      (φ ∘ physicalSpectatorReindexAt i) p =
      splitGrushin c oscillatorBasis B φ (physicalSpectatorReindexAt i p) := by
  have h := physicalSpectatorReindexAt_combinedCutoffScalar i c hφ p
  simp only [combinedCutoffScalar, yDir, tDir] at h
  simp only [splitGrushin, Function.comp_apply]
  change -_ - _ + B (physicalSpectatorReindexAt i p) * φ (physicalSpectatorReindexAt i p) = _
  simp only [ksBasis, oscillatorBasis, spectatorBasis, EuclideanSpace.single, PiLp.single] at h ⊢
  linear_combination -h

theorem physicalSpectatorReindexAt_weak_equation (i : Fin 2) (c : ℝ)
    {Ω : Set (Space (Fin 3))} (B : NuclearKSSpace i → ℝ)
    (f src : NuclearKSSpace i → ℂ)
    (hEq : ∀ φ : NuclearKSSpace i → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ physicalSpectatorReindexAt i ⁻¹' Ω →
      Integrable (fun p => splitGrushin c spectatorBasis B φ p • f p) volume ∧
      Integrable (fun p => φ p • src p) volume ∧
      (∫ p, splitGrushin c spectatorBasis B φ p • f p) = ∫ p, φ p • src p) :
    ∀ φ : Space (Fin 3) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      Integrable (fun p => splitGrushin c oscillatorBasis
        (B ∘ (physicalSpectatorReindexAt i).symm) φ p •
        f ((physicalSpectatorReindexAt i).symm p)) volume ∧
      Integrable (fun p => φ p • src ((physicalSpectatorReindexAt i).symm p)) volume ∧
      (∫ p, splitGrushin c oscillatorBasis (B ∘ (physicalSpectatorReindexAt i).symm) φ p •
        f ((physicalSpectatorReindexAt i).symm p)) =
        ∫ p, φ p • src ((physicalSpectatorReindexAt i).symm p) := by
  intro φ hφ hc hs
  obtain ⟨hφR, hcR, htR⟩ := physicalSpectatorReindexAt_cutoff_test i hφ hc
  have hBR : (B ∘ (physicalSpectatorReindexAt i).symm) ∘ physicalSpectatorReindexAt i = B := by
    ext p
    simp only [Function.comp_apply, LinearIsometryEquiv.symm_apply_apply]
  have hOp (p : NuclearKSSpace i) :=
    physicalSpectatorReindexAt_splitGrushin i c (B ∘ (physicalSpectatorReindexAt i).symm) hφ p
  rw [hBR] at hOp
  obtain ⟨hL, hR, hE⟩ := hEq (φ ∘ physicalSpectatorReindexAt i) hφR hcR (by
    rw [htR]
    exact Set.preimage_mono hs)
  let L : Space (Fin 3) → ℂ := fun p =>
    splitGrushin c oscillatorBasis (B ∘ (physicalSpectatorReindexAt i).symm) φ p •
      f ((physicalSpectatorReindexAt i).symm p)
  let R : Space (Fin 3) → ℂ := fun p => φ p • src ((physicalSpectatorReindexAt i).symm p)
  have hLc : (L ∘ physicalSpectatorReindexAt i) =
      fun p => splitGrushin c spectatorBasis B (φ ∘ physicalSpectatorReindexAt i) p • f p := by
    ext p
    simp only [L, Function.comp_apply, LinearIsometryEquiv.symm_apply_apply, hOp]
  have hRc : (R ∘ physicalSpectatorReindexAt i) =
      fun p => (φ ∘ physicalSpectatorReindexAt i) p • src p := by
    ext p
    simp only [R, Function.comp_apply, LinearIsometryEquiv.symm_apply_apply]
  have hp := physicalSpectatorReindexAt_measurePreserving i
  have hm := (physicalSpectatorReindexAt i).toHomeomorph.measurableEmbedding
  have hiL : Integrable L volume := (hp.integrable_comp_emb hm).mp (hLc.symm ▸ hL)
  have hiR : Integrable R volume := (hp.integrable_comp_emb hm).mp (hRc.symm ▸ hR)
  refine ⟨hiL, hiR, ?_⟩
  change (∫ p, L p) = ∫ p, R p
  rw [← hp.integral_comp hm L, ← hp.integral_comp hm R]
  change (∫ p, (L ∘ physicalSpectatorReindexAt i) p) = ∫ p, (R ∘ physicalSpectatorReindexAt i) p
  rw [hLc, hRc]
  exact hE

end TheoremT.Continuum
