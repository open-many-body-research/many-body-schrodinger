import WeakGrushinSpectatorTestData_v1
import WeakGrushinSpectatorSmoothCommute_v1

/-! Actual weak spectator differentiation of the local Grushin equation.
No second derivatives of the weak solution are assumed. Both the original
weak equations and the conclusion use all genuine compact smooth tests. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

set_option maxHeartbeats 800000 in
theorem local_weak_grushin_spectator_differentiate (c : ℝ)
    {Ω : Set (Space κ)} (G d h k : Space κ → ℂ)
    (hG : ProductLocallyL2On G Ω) (hd : ProductLocallyL2On d Ω)
    (hh : ProductLocallyL2On h Ω) (hk : ProductLocallyL2On k Ω)
    (v : EuclideanSpace ℝ κ)
    (hD : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, φ p • d p) = -(∫ p, fderiv ℝ φ p (0,v) • G p))
    (hP : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • G p) = ∫ p, φ p • h p)
    (hhD : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, φ p • k p) = -(∫ p, fderiv ℝ φ p (0,v) • h p)) :
    ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      Integrable (fun p => splitGrushin c oscillatorBasis (fun _ => 0) φ p • d p) ∧
      Integrable (fun p => φ p • k p) ∧
      (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • d p) = ∫ p, φ p • k p := by
  intro φ hφ hcφ hsφ
  have hiP : Integrable (fun p => splitGrushin c oscillatorBasis (fun _ => 0) φ p • d p) :=
    product_locallyL2_compact_smul_integrable d hd
      (splitGrushin_continuous c oscillatorBasis continuous_const hφ)
      (splitGrushin_compact c oscillatorBasis (fun _ => 0) hcφ)
      ((splitGrushin_test_tsupport_subset c φ).trans hsφ)
  have hik := product_locallyL2_compact_smul_integrable k hk hφ.continuous hcφ hsφ
  refine ⟨hiP,hik,?_⟩
  have hDφ : ContDiff ℝ ∞ (fun p => fderiv ℝ φ p (0,v)) := partialTDirectional_contDiff hφ v
  have hcDφ : HasCompactSupport (fun p => fderiv ℝ φ p (0,v)) := hcφ.fderiv_apply ℝ (0,v)
  have hsDφ : tsupport (fun p => fderiv ℝ φ p (0,v)) ⊆ Ω :=
    (tsupport_fderiv_apply_subset ℝ (0,v)).trans hsφ
  have hPφ := splitGrushin_zero_contDiff c oscillatorBasis hφ
  have hcPφ := splitGrushin_compact c oscillatorBasis (fun _ => 0) hcφ
  have hsPφ := (splitGrushin_test_tsupport_subset c φ).trans hsφ
  calc
    _ = -(∫ p, fderiv ℝ (splitGrushin c oscillatorBasis (fun _ => 0) φ) p (0,v) • G p) :=
      hD _ hPφ hcPφ hsPφ
    _ = -(∫ p, splitGrushin c oscillatorBasis (fun _ => 0)
        (fun q => fderiv ℝ φ q (0,v)) p • G p) := by
      apply congrArg Neg.neg
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun p =>
        congrArg (fun a : ℝ => a • G p)
          (splitGrushin_spectator_directional_commute c oscillatorBasis v hφ p).symm)
    _ = -(∫ p, fderiv ℝ φ p (0,v) • h p) := congrArg Neg.neg (hP _ hDφ hcDφ hsDφ)
    _ = _ := (hhD φ hφ hcφ hsφ).symm

#print axioms local_weak_grushin_spectator_differentiate
end TheoremT.Continuum.WeakGrushin
