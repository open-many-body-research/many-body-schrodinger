import SpectatorIterationState_v1

/-! Explicit geometric data for one finite spectator stage.  This predicate
contains only open-region, smooth-cutoff and pointwise coefficient bounds;
it contains no regularity estimate or derivative conclusion. -/
noncomputable section
open scoped ContDiff
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

def SpectatorStepGeometry (c : ℝ) (Ω O W : Set (Space κ))
    (χ η : Space κ → ℝ) (M A B D Q : ℝ) : Prop :=
  IsOpen Ω ∧ ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
  ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧ tsupport η ⊆ Ω ∧
  IsOpen W ∧ tsupport χ ⊆ W ∧ (∀ p ∈ W, η p = 1) ∧
  0 ≤ B ∧ 0 ≤ D ∧ 0 ≤ Q ∧ (∀ p, |χ p| ≤ M) ∧
  (∀ p ∈ tsupport χ, |combinedCutoffScalar c χ p| ≤ A) ∧
  (∀ p ∈ tsupport χ, cutoffGradientWeight c χ p ≤ B) ∧
  (∀ p, (η p)^2 ≤ D) ∧ (∀ p, grushinCutoffWeight c η p ≤ Q) ∧
  ∀ p ∈ O, χ p = 1

theorem SpectatorStepGeometry.domain_subset
    {c : ℝ} {Ω O W : Set (Space κ)} {χ η : Space κ → ℝ} {M A B D Q : ℝ}
    (h : SpectatorStepGeometry c Ω O W χ η M A B D Q) : O ⊆ Ω := by
  obtain ⟨_,_,_,_,_,hηΩ,_,hχW,hη1,_,_,_,_,_,_,_,_,hχ1⟩ := h
  intro p hp
  apply hηΩ
  apply subset_tsupport η
  change η p ≠ 0
  have hx : p ∈ tsupport χ := by
    apply subset_tsupport χ
    change χ p ≠ 0
    rw [hχ1 p hp]
    norm_num
  rw [hη1 p (hχW hx)]
  norm_num

#print axioms SpectatorStepGeometry.domain_subset
end TheoremT.Continuum.WeakGrushin
