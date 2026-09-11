import GrushinLocalL2Neighborhood_v1
import WeakGrushinJetFields_v1

/-! Locality and integrability of the actual tests used in spectator
commutation. Raw local L2 inputs have ordinary integrable compact-test pairings. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem splitGrushin_test_tsupport_subset (c : ℝ) (φ : Space κ → ℝ) :
    tsupport (splitGrushin c oscillatorBasis (fun _ => 0) φ) ⊆ tsupport φ := by
  apply closure_minimal ?_ (isClosed_tsupport φ)
  intro p hp
  by_contra hn
  exact hp (splitGrushin_zero_off_test c oscillatorBasis (fun _ => 0) hn)

theorem local_spectator_test_integrable
    {Ω : Set (Space κ)} (h k : Space κ → ℂ)
    (hh : ProductLocallyL2On h Ω) (hk : ProductLocallyL2On k Ω)
    (v : EuclideanSpace ℝ κ)
    {φ : Space κ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ Ω) :
    Integrable (fun p => φ p • k p) ∧
    Integrable (fun p => fderiv ℝ φ p (0,v) • h p) := by
  exact ⟨product_locallyL2_compact_smul_integrable k hk hφ.continuous hcφ hsφ,
    product_locallyL2_compact_smul_integrable h hh
      (partialTDirectional_contDiff hφ v).continuous
      (partialTDirectional_hasCompactSupport hcφ v)
      ((tsupport_fderiv_apply_subset ℝ (0,v)).trans hsφ)⟩

#print axioms splitGrushin_test_tsupport_subset
#print axioms local_spectator_test_integrable
end TheoremT.Continuum.WeakGrushin
